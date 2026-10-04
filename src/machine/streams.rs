use crate::arena::opt_in_buf_reader::*;
use crate::arena::stream_layout::*;
use crate::functor_macro::*;
use crate::machine::*;
use crate::parser::ast::ParserError;
use crate::types::*;
use crate::{machine::machine_state::MachineState, types::HeapCellValue};

use std::fs::OpenOptions;
use std::io::ErrorKind;

impl MachineState {
    #[inline]
    pub(crate) fn eof_action(
        &mut self,
        result: HeapCellValue,
        mut stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> CallResult {
        let eof_action = stream.options.eof_action();

        match eof_action {
            EOFAction::Error => {
                stream.past_end_of_stream = true;
                Err(self.open_past_eos_error(stream, caller, arity))
            }
            EOFAction::EOFCode => {
                let end_of_stream = if stream.options.stream_type() == StreamType::Binary {
                    fixnum_as_cell!(Fixnum::build_with(-1))
                } else {
                    atom_as_cell!(atom!("end_of_file"))
                };

                stream.past_end_of_stream = true;
                unify!(self, result, end_of_stream);
                Ok(())
            }
            EOFAction::Reset => {
                if !stream.reset_layout() {
                    stream.past_end_of_stream = true;
                }

                self.fail = stream.past_end_of_stream;
                Ok(())
            }
        }
    }

    /// ## Warning
    ///
    /// The options of streams stored in `Machine::indices` should only
    /// be modified through [`IndexStore::update_stream_options`].
    pub(crate) fn get_stream_options(
        &mut self,
        alias: HeapCellValue,
        eof_action: HeapCellValue,
        reposition: HeapCellValue,
        stream_type: HeapCellValue,
    ) -> StreamOptions {
        let alias = read_heap_cell!(self.store(MachineState::deref(self, alias)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                if name != atom!("[]") {
                    Some(name)
                } else {
                    None
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                if name != atom!("[]") {
                    Some(name)
                } else {
                    None
                }
            }
            _ => {
                None
            }
        );

        let eof_action = read_heap_cell!(self.store(MachineState::deref(self, eof_action)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                match name  {
                    atom!("eof_code") => EOFAction::EOFCode,
                    atom!("error") => EOFAction::Error,
                    atom!("reset") => EOFAction::Reset,
                    _ => unreachable!(),
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                match name  {
                    atom!("eof_code") => EOFAction::EOFCode,
                    atom!("error") => EOFAction::Error,
                    atom!("reset") => EOFAction::Reset,
                    _ => unreachable!(),
                }
            }
            _ => {
                unreachable!()
            }
        );

        let reposition = read_heap_cell!(self.store(MachineState::deref(self, reposition)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                name == atom!("true")
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                name == atom!("true")
            }
            _ => {
                unreachable!()
            }
        );

        let stream_type = read_heap_cell!(self.store(MachineState::deref(self, stream_type)),
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);
                match name {
                    atom!("text") => StreamType::Text,
                    atom!("binary") => StreamType::Binary,
                    _ => unreachable!(),
                }
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);
                match name {
                    atom!("text") => StreamType::Text,
                    atom!("binary") => StreamType::Binary,
                    _ => unreachable!(),
                }
            }
            _ => {
                unreachable!()
            }
        );

        let mut options = StreamOptions::default();

        options.set_stream_type(stream_type);
        options.set_reposition(reposition);
        options.set_alias_to_atom_opt(alias);
        options.set_eof_action(eof_action);

        options
    }

    /// If `addr` is a [`Cons`](HeapCellValueTag::Cons) to a stream, then returns it.
    ///
    /// If it is an atom or a string, then this searches for the corresponding stream
    /// inside of [`self.indices`], returning it.
    ///
    /// ## Warning
    ///
    /// **Do not directly modify [`stream.options`](Stream::options_mut)
    /// on the returned stream.**
    ///
    /// Other functions rely on the invariants of [`IndexStore`], which may
    /// become invalidated by the direct modification of a stream's option (namely,
    /// its alias name). Instead, use [`IndexStore::update_stream_options`].
    pub(crate) fn get_stream_or_alias(
        &mut self,
        addr: HeapCellValue,
        indices: &IndexStore,
        caller: Atom,
        arity: usize,
    ) -> Result<Stream, MachineStub> {
        let addr = self.store(MachineState::deref(self, addr));

        read_heap_cell!(addr,
            (HeapCellValueTag::Atom, (name, arity)) => {
                debug_assert_eq!(arity, 0);

                return match indices.get_stream(name) {
                    Some(stream) => Ok(stream),
                    _ => {
                        let stub = functor_stub(caller, arity);
                        let addr = atom_as_cell!(name);
                        let existence_error = self.existence_error(ExistenceError::Stream(addr));

                        Err(self.error_form(existence_error, stub))
                    }
                };
            }
            (HeapCellValueTag::Str, s) => {
                let (name, arity) = cell_as_atom_cell!(self.heap[s])
                    .get_name_and_arity();

                debug_assert_eq!(arity, 0);

                return match indices.get_stream(name) {
                    Some(stream) => Ok(stream),
                    _ => {
                        let stub = functor_stub(caller, arity);
                        let addr = atom_as_cell!(name);

                        let existence_error = self.existence_error(ExistenceError::Stream(addr));

                        Err(self.error_form(existence_error, stub))
                    }
                };
            }
            (HeapCellValueTag::Cons, cons_ptr) => {
                if matches!(cons_ptr.get_tag(), ArenaHeaderTag::Dropped) {
                    let stub = functor_stub(caller, arity);
                    let err = self.existence_error(ExistenceError::Stream(addr));

                    return Err(self.error_form(err, stub));
                } else if let Some(stream) = Stream::from_tag(cons_ptr) {
                    return Ok(stream);
                }
            }
            _ => {
            }
        );

        let stub = functor_stub(caller, arity);

        if addr.is_var() {
            let instantiation_error = self.instantiation_error();
            Err(self.error_form(instantiation_error, stub))
        } else {
            let domain_error = self.domain_error(DomainErrorType::StreamOrAlias, addr);
            Err(self.error_form(domain_error, stub))
        }
    }

    pub(crate) fn open_parsing_stream(
        &mut self,
        mut stream: Stream,
    ) -> Result<Stream, ParserError> {
        match stream.peek_char() {
            Ok(None) => Ok(stream), // empty stream is handled gracefully by Lexer::eof
            Err(e) => Err(ParserError::from(e)),
            Ok(Some(c)) => {
                if c == '\u{feff}' {
                    // skip UTF-8 BOM
                    stream.read_char()?;
                }

                Ok(stream)
            }
        }
    }

    pub(crate) fn stream_permission_error(
        &mut self,
        perm: Permission,
        err_atom: Atom,
        stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(caller, arity);
        let err = self.permission_error(
            perm,
            err_atom,
            if let Some(alias) = stream.options.get_alias() {
                atom_as_cell!(alias)
            } else {
                stream.into()
            },
        );

        self.error_form(err, stub)
    }

    #[inline]
    pub(crate) fn open_past_eos_error(
        &mut self,
        stream: Stream,
        caller: Atom,
        arity: usize,
    ) -> MachineStub {
        self.stream_permission_error(
            Permission::InputStream,
            atom!("past_end_of_stream"),
            stream,
            caller,
            arity,
        )
    }

    pub(crate) fn open_permission_error<T: PermissionError>(
        &mut self,
        culprit: T,
        stub_name: Atom,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);
        let err = self.permission_error(Permission::Open, atom!("source_sink"), culprit);

        self.error_form(err, stub)
    }

    pub(crate) fn occupied_alias_permission_error(
        &mut self,
        alias: Atom,
        stub_name: Atom,
        stub_arity: usize,
    ) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);

        let err = self.permission_error(
            Permission::Open,
            atom!("source_sink"),
            functor!(atom!("alias"), [atom_as_cell(alias)]),
        );

        self.error_form(err, stub)
    }

    pub(crate) fn reposition_error(&mut self, stub_name: Atom, stub_arity: usize) -> MachineStub {
        let stub = functor_stub(stub_name, stub_arity);
        let rep_stub = functor!(atom!("reposition"), [atom_as_cell((atom!("true")))]);
        let err = self.permission_error(Permission::Open, atom!("source_sink"), rep_stub);

        self.error_form(err, stub)
    }

    pub(crate) fn check_stream_properties(
        &mut self,
        stream: Stream,
        expected_type: StreamType,
        input: Option<HeapCellValue>,
        caller: Atom,
        arity: usize,
    ) -> CallResult {
        let opt_err = if input.is_some() && !stream.is_input_stream()
            || input.is_none() && !stream.is_output_stream()
        {
            Some(atom!("stream")) // 8.14.2.3 g)
        } else if stream.options.stream_type() != expected_type {
            Some(expected_type.other().as_atom()) // 8.14.2.3 h)
        } else {
            None
        };

        let permission = if input.is_some() {
            Permission::InputStream
        } else {
            Permission::OutputStream
        };

        if let Some(err_atom) = opt_err {
            return Err(self.stream_permission_error(permission, err_atom, stream, caller, arity));
        }

        if let Some(input) = input
            && stream.past_end_of_stream
        {
            self.eof_action(input, stream, caller, arity)?;
        }

        Ok(())
    }

    pub(crate) fn stream_from_file_spec(
        &mut self,
        file_spec: Atom,
        indices: &mut IndexStore,
        options: &StreamOptions,
    ) -> Result<Stream, MachineStub> {
        if file_spec == atom!("") {
            let stub = functor_stub(atom!("open"), 4);
            let err = self.domain_error(DomainErrorType::SourceSink, self.registers[1]);

            return Err(self.error_form(err, stub));
        }

        // 8.11.5.3l)
        if let Some(alias) = options.get_alias()
            && indices.has_stream(alias)
        {
            return Err(self.occupied_alias_permission_error(alias, atom!("open"), 4));
        }

        let mode = cell_as_atom!(self.store(MachineState::deref(self, self.registers[2])));
        let mut open_options = OpenOptions::new();

        let (is_input_file, in_append_mode) = match mode {
            atom!("read") => {
                open_options.read(true).write(false).create(false);
                (true, false)
            }
            atom!("write") => {
                open_options
                    .read(false)
                    .write(true)
                    .truncate(true)
                    .create(true);

                (false, false)
            }
            atom!("append") => {
                open_options
                    .read(false)
                    .write(true)
                    .create(true)
                    .append(true);

                (false, true)
            }
            _ => {
                let stub = functor_stub(atom!("open"), 4);
                let err = self.domain_error(DomainErrorType::IOMode, self[temp_v!(2)]);

                // 8.11.5.3h)
                return Err(self.error_form(err, stub));
            }
        };

        let mut path = PathBuf::from(&*file_spec.as_str());

        loop {
            let file = match open_options.open(&path) {
                Ok(file) => file,
                Err(err) => {
                    match err.kind() {
                        ErrorKind::NotFound => {
                            // 8.11.5.3j)
                            let stub = functor_stub(atom!("open"), 4);

                            let err =
                                self.existence_error(ExistenceError::SourceSink(self[temp_v!(1)]));

                            return Err(self.error_form(err, stub));
                        }
                        ErrorKind::PermissionDenied => {
                            // 8.11.5.3k)
                            return Err(self.open_permission_error(
                                self.registers[1],
                                atom!("open"),
                                4,
                            ));
                        }
                        _ => {
                            // assume the OS is out of file descriptors.
                            let stub = functor_stub(atom!("open"), 4);
                            let err = Self::resource_error(ResourceError::OutOfFiles);

                            return Err(self.error_form(err, stub));
                        }
                    }
                }
            };

            if path.extension().is_none()
                && let Ok(metadata) = file.metadata()
                && metadata.is_dir()
            {
                path.set_extension("pl");
                continue;
            }

            return Ok(if is_input_file {
                Stream::from_file_as_input(file_spec, file, &mut self.arena)
            } else {
                Stream::from_file_as_output(file_spec, file, in_append_mode, &mut self.arena)
            });
        }
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use std::{cell::RefCell, io::Read, io::Write, rc::Rc};

    use crate::LeafAnswer;
    use crate::machine::config::*;

    fn succeeded<T>(answer: Vec<Result<LeafAnswer, T>>) -> bool {
        // Ideally this should be a method in QueryState or LeafAnswer.
        matches!(
            answer[0].as_ref(),
            Ok(LeafAnswer::True) | Ok(LeafAnswer::LeafAnswer { .. })
        )
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_input_string_stream() {
        let streams =
            StreamConfig::default().with_user_input(InputStreamConfig::string("a(1,2,3)."));

        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_input(_), \+ at_end_of_stream."#)
            .collect();

        assert!(succeeded(complete_answer));

        let complete_answer: Vec<_> = machine.run_query("read(A).").collect();

        assert_eq!(
            complete_answer,
            [Ok(LeafAnswer::from_bindings([(
                "A",
                Term::compound("a", [Term::integer(1), Term::integer(2), Term::integer(3),])
            )]))]
        );

        let complete_answer: Vec<_> = machine.run_query(r#"at_end_of_stream."#).collect();

        assert!(succeeded(complete_answer));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_input_channel_stream() {
        let (mut user_input, channel_stream) = InputStreamConfig::channel();
        let streams = StreamConfig::default().with_user_input(channel_stream);
        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_input(_), \+ at_end_of_stream."#)
            .collect();

        assert!(succeeded(complete_answer));

        write!(user_input, "a(1,2,3).").unwrap();

        let complete_answer: Vec<_> = machine
            .run_query(r#"\+ at_end_of_stream, read(A)."#)
            .collect();

        assert_eq!(
            complete_answer,
            [Ok(LeafAnswer::from_bindings([(
                "A",
                Term::compound("a", [Term::integer(1), Term::integer(2), Term::integer(3),])
            )]))]
        );

        // End-of-data but not end-of-stream;
        let complete_answer: Vec<_> = machine
            .run_query(
                r#"
                use_module(library(charsio)),
                current_input(In), get_n_chars(In, N, C),
                N == 0, \+ at_end_of_stream.
            "#,
            )
            .collect();

        assert!(succeeded(complete_answer));

        // Dropping the sender closes the input
        drop(user_input);

        let complete_answer: Vec<_> = machine
            .run_query(
                r#"
                current_input(In), get_n_chars(In, N, _),
                N == 0, at_end_of_stream.
            "#,
            )
            .collect();

        assert!(succeeded(complete_answer));
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn user_output_callback_stream() {
        let test_string = Rc::new(RefCell::new(String::new()));

        let streams =
            StreamConfig::default().with_user_output(OutputStreamConfig::callback(Box::new({
                let test_string = test_string.clone();
                move |x| {
                    x.read_to_string(&mut test_string.borrow_mut()).unwrap();
                }
            })));

        let mut machine = MachineBuilder::default().with_streams(streams).build();

        let complete_answer: Vec<_> = machine
            .run_query(r#"current_output(Out), \+ at_end_of_stream(Out)."#)
            .collect();

        assert!(succeeded(complete_answer));

        let complete_answer: Vec<_> = machine
            .run_query(r#"write(asdf), nl, flush_output."#)
            .collect();

        assert!(succeeded(complete_answer));
        assert_eq!(test_string.borrow().as_str(), "asdf\n");

        let complete_answer: Vec<_> = machine.run_query(r#"write(abcd), flush_output."#).collect();

        assert!(succeeded(complete_answer));
        assert_eq!(test_string.borrow().as_str(), "asdf\nabcd");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_memory_user_output_stream() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query(
                "\\+ \\+ (current_output(Stream), close(Stream)), write(user_output, hello).",
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());

        let mut actual = String::new();
        machine.user_output.read_to_string(&mut actual).unwrap();
        assert_eq!(actual, "hello");
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_memory_user_output_stream_twice() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query("\\+ \\+ (current_output(Stream), close(Stream), close(Stream)).")
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_realiased_stream() {
        let mut machine = MachineBuilder::new().build();

        let results = machine
            .run_query(
                r#"
                \+ \+ (
                    open("README.md", read, S, [alias(readme)]),
                    open(stream(S), read, _, [alias(another_alias)]),
                    close(S)
                ),
                open("README.md", read, _, [alias(readme)]).
            "#,
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn close_realiased_user_output() {
        let mut machine = MachineBuilder::new()
            .with_streams(StreamConfig::in_memory())
            .build();

        let results = machine
            .run_query(
                r#"
                \+ \+ (
                    open("README.md", read, S),
                    open(stream(S), read, _, [alias(user_output)]),
                    close(S)
                ),
                write(user_output, hello).
            "#,
            )
            .collect::<Vec<_>>();

        assert_eq!(results.len(), 1);
        assert!(results[0].is_ok());
    }
}
