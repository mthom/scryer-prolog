use crate::machine::Number;
use crate::Machine;
use ordered_float::OrderedFloat;
use puruspe::beta::*;
use puruspe::error::*;
use puruspe::gamma::*;

macro_rules! number_as_f64 {
    ($self: ident, $reg: literal) => {{
        match Number::try_from(($self.deref_register($reg), &$self.machine_st.arena.f64_tbl)) {
            Ok(Number::Float(n)) => n.into_inner(),
            Ok(Number::Fixnum(n)) => n.get_num() as f64,
            Ok(Number::Integer(n)) => n.to_f64().value(),
            _ => {
                unreachable!()
            }
        }
    }};
}

macro_rules! return_f64_reg {
    ($self: ident, $val: ident, $reg: literal) => {{
        let return_value = $self.deref_register($reg);
        $self.machine_st.unify_f64($val, return_value);
    }};
}

impl Machine {
    #[inline(always)]
    pub(crate) fn erf(&mut self) {
        let x = number_as_f64!(self, 1);
        let erf_x = float_alloc!(erf(x), self.machine_st.arena);
        return_f64_reg!(self, erf_x, 2);
    }

    #[inline(always)]
    pub(crate) fn erfc(&mut self) {
        let x = number_as_f64!(self, 1);
        let erfc_x = float_alloc!(erfc(x), self.machine_st.arena);
        return_f64_reg!(self, erfc_x, 2);
    }

    #[inline(always)]
    pub(crate) fn inverf(&mut self) {
        let erf_x = number_as_f64!(self, 1);
        let x = float_alloc!(inverf(erf_x), self.machine_st.arena);
        return_f64_reg!(self, x, 2);
    }

    #[inline(always)]
    pub(crate) fn inverfc(&mut self) {
        let erfc_x = number_as_f64!(self, 1);
        let x = float_alloc!(inverfc(erfc_x), self.machine_st.arena);
        return_f64_reg!(self, x, 2);
    }

    #[inline(always)]
    pub(crate) fn gamma(&mut self) {
        let x = number_as_f64!(self, 1);
        let gamma_x = float_alloc!(gamma(x), self.machine_st.arena);
        return_f64_reg!(self, gamma_x, 2);
    }

    #[inline(always)]
    pub(crate) fn gammp(&mut self) {
        let a = number_as_f64!(self, 1);
        let x = number_as_f64!(self, 2);
        let gammp_a_x = float_alloc!(gammp(a, x), self.machine_st.arena);
        return_f64_reg!(self, gammp_a_x, 3);
    }

    #[inline(always)]
    pub(crate) fn gammq(&mut self) {
        let a = number_as_f64!(self, 1);
        let x = number_as_f64!(self, 2);
        let gammq_a_x = float_alloc!(gammq(a, x), self.machine_st.arena);
        return_f64_reg!(self, gammq_a_x, 3);
    }

    #[inline(always)]
    pub(crate) fn invgammp(&mut self) {
        let p = number_as_f64!(self, 1);
        let a = number_as_f64!(self, 2);
        let x = float_alloc!(invgammp(p, a), self.machine_st.arena);
        return_f64_reg!(self, x, 3);
    }

    #[inline(always)]
    pub(crate) fn ln_gamma(&mut self) {
        let x = number_as_f64!(self, 1);
        let ln_gamma_x = float_alloc!(ln_gamma(x), self.machine_st.arena);
        return_f64_reg!(self, ln_gamma_x, 2);
    }

    #[inline(always)]
    pub(crate) fn beta(&mut self) {
        let x = number_as_f64!(self, 1);
        let y = number_as_f64!(self, 2);
        let beta_x_y = float_alloc!(beta(x, y), self.machine_st.arena);
        return_f64_reg!(self, beta_x_y, 3);
    }

    #[inline(always)]
    pub(crate) fn betai(&mut self) {
        let a = number_as_f64!(self, 1);
        let b = number_as_f64!(self, 2);
        let x = number_as_f64!(self, 3);
        let betai_a_b_x = float_alloc!(betai(a, b, x), self.machine_st.arena);
        return_f64_reg!(self, betai_a_b_x, 4);
    }

    #[inline(always)]
    pub(crate) fn invbetai(&mut self) {
        let a = number_as_f64!(self, 1);
        let b = number_as_f64!(self, 2);
        let p = number_as_f64!(self, 3);
        let x = float_alloc!(invbetai(a, b, p), self.machine_st.arena);
        return_f64_reg!(self, x, 4);
    }
}
