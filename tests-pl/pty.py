#!/usr/bin/env python
# A simple script to simulate terminal environment
# From: https://unix.stackexchange.com/questions/249723/how-to-trick-a-command-into-thinking-its-output-is-going-to-a-terminal#answer-564841

from sys import argv
import os
import signal

# I've had problems with python's File objects at this low a level, so
# we're going to use integers to specify all files in this script.
stdin = 0
stdout = 1
stderr = 2
# Include this if passing the command and arguments to fish to
# prevent fish from applying any expansions.
#import re
#def fish_escape(args):
#    def escape_one(arg):
#        return "'" + re.sub(r"('|\\)", r'\\\1', arg) + "'"
#    escaped_args = map(escape_one, args)
#    return ' '.join(escaped_args)

if len(argv) < 2:
    os.write(stderr,
b"""A tragically beautiful piece of hackery, made to fool programs like ls,
grep, rg, and fd into thinking they're actually connected to a terminal.
Its usage:

pty command [arg1 arg2 ...]

Examples:
pty ls --color -R | less -r
git log -p | pty rg <search terms> | less -r
""")
    exit(255)

# We do not use forkpty here because it would block ^Cs from reaching the
# child process. And we don't need that.
ptm, pts = os.openpty()
pid = os.fork()
if pid == 0:
    # The child runs this.
    # To get the behaviour we want, we only need to replace the process's
    # stdout with pts. Everything else should remain in place, so that things
    # like `ps -eF | pty rg python | less -r` will still work as intended.
    os.dup2(pts, stdout)
    # This is not like a subprocess.call(). It replaces the entire child
    # process with argv[1:], meaning execvp will not return! Web search
    # "fork exec" for more.
    #print(argv)
    os.execvp(argv[1], argv[1:])
    # Use this if calling fish.
    #os.execvp('fish', ['fish', '-c', fish_escape(argv[1:])])


# The parent runs this.

# If the parent doesn't close the slave end, the script won't be able to
# exit. The next read on ptm after the child process terminates would hang
# forever because pts would technically still be open.
os.close(pts)

# The whole process group gets SIGINT, including the child, so we don't need
# to react to it. We'll know when to leave, judging by what the child does.
signal.signal(signal.SIGINT, signal.SIG_IGN)

while True:
    try:
        chunk = os.read(ptm, 4096)
    except OSError:
        break
    try:
        os.write(stdout, chunk)
    except BrokenPipeError:
        # This happens when the parent is piping output to another process in a
        # pipeline, like in `pty ls --color -R | less -r`, and the receiving
        # process is terminated before the child has exited. If the receiving
        # process is less, this can happen very easily. It happens every time
        # the user decides to quit less before it has displayed all output. So,
        # we need to stop the child process now.
        os.kill(pid, signal.SIGTERM)
        # Also close the child's inputs and outputs, just in case it is
        # blocking on them and can't react to the SIGTERM as a result.
        os.close(ptm)
        break
wait_pid, status = os.waitpid(pid, 0)
exit(status >> 8)