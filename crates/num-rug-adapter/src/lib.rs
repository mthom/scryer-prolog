use num_bigint::{BigInt, ParseBigIntError};
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{FromPrimitive, Num, Signed, ToPrimitive};
use num_traits::identities::One;

use std::cmp::Ordering;
use std::fmt::{self, Display, Formatter};
use std::ops::*;

use std::str::FromStr;

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Integer(BigInt);

impl Integer {
    #[inline]
    pub fn new() -> Self {
        Integer(BigInt::default())
    }

    #[inline]
    pub fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        BigInt::from_str_radix(s, radix).map(Integer)
    }

    #[inline]
    pub fn to_u8(&self) -> Option<u8> {
        self.0.to_u8()
    }

    #[inline]
    pub fn to_u32(&self) -> Option<u32> {
        self.0.to_u32()
    }

    #[inline]
    pub fn to_u64(&self) -> Option<u64> {
        self.0.to_u64()
    }

    #[inline]
    pub fn to_usize(&self) -> Option<usize> {
        self.0.to_usize()
    }

    #[inline]
    pub fn to_i32(&self) -> Option<i32> {
        self.0.to_i32()
    }

    #[inline]
    pub fn to_isize(&self) -> Option<isize> {
        self.0.to_isize()
    }

    #[inline]
    pub fn to_f64(&self) -> f64 {
        self.0.to_f64().unwrap()
    }

    #[inline]
    pub fn abs(&self) -> Self {
        Integer(self.0.abs())
    }

    #[inline]
    pub fn abs_ref(&self) -> Self {
        Integer(self.0.abs())
    }

    #[inline]
    pub fn div_rem(&self, other: Self) -> (Self, Self) {
        let (a, b) = num_integer::Integer::div_rem(&self.0, &other.0);
        (Integer(a), Integer(b))
    }

    #[inline]
    pub fn div_rem_ref(&self, other: &Self) -> (Self, Self) {
        let (a, b) = num_integer::Integer::div_rem(&self.0, &other.0);
        (Integer(a), Integer(b))
    }

    #[inline]
    pub fn div_rem_floor(&self, other: Self) -> (Self, Self) {
        let (a, b) = num_integer::Integer::div_mod_floor(&self.0, &other.0);
        (Integer(a), Integer(b))
    }

    #[inline]
    pub fn div_rem_floor_ref(&self, other: &Self) -> (Self, Self) {
        let (a, b) = num_integer::Integer::div_mod_floor(&self.0, &other.0);
        (Integer(a), Integer(b))
    }

    #[inline]
    pub fn mod_u(&self, modulo: u32) -> u32 {
        (self.0.abs() % modulo).to_u32().unwrap()
    }

    #[inline]
    pub fn is_odd(&self) -> bool {
        num_integer::Integer::is_odd(&self.0)
    }

    #[inline]
    pub fn from_f64(v: f64) -> Option<Self> {
        BigInt::from_f64(v).map(Integer)
    }

    #[inline]
    pub fn gcd_ref(&self, other: &Self) -> Self {
        Integer(num_integer::Integer::gcd(&self.0, &other.0))
    }

    #[inline]
    pub fn gcd(&self, other: &Self) -> Self {
        Integer(num_integer::Integer::gcd(&self.0, &other.0))
    }
}

impl From<&Integer> for Integer {
    #[inline]
    fn from(s: &Integer) -> Self {
        s.clone()
    }
}

impl From<i32> for Integer {
    #[inline]
    fn from(s: i32) -> Self {
        Integer(BigInt::from(s))
    }
}

impl From<isize> for Integer {
    #[inline]
    fn from(s: isize) -> Self {
        Integer(BigInt::from(s))
    }
}

impl From<u8> for Integer {
    #[inline]
    fn from(s: u8) -> Self {
        Integer(BigInt::from(s))
    }
}

impl From<u32> for Integer {
    #[inline]
    fn from(s: u32) -> Self {
        Integer(BigInt::from(s))
    }
}

impl From<u64> for Integer {
    #[inline]
    fn from(s: u64) -> Self {
        Integer(BigInt::from(s))
    }
}

impl From<usize> for Integer {
    #[inline]
    fn from(s: usize) -> Self {
        Integer(BigInt::from(s))
    }
}

impl Mul for Integer {
    type Output = Integer;

    #[inline]
    fn mul(self, other: Integer) -> Self::Output {
        Integer(self.0 * other.0)
    }
}

impl Mul<u32> for Integer {
    type Output = Integer;

    #[inline]
    fn mul(self, other: u32) -> Self::Output {
        Integer(self.0 * other)
    }
}

impl Mul<&Integer> for Integer {
    type Output = Integer;

    fn mul(self, other: &Integer) -> Self::Output {
        Integer(self.0 * &other.0)
    }
}

impl MulAssign<&Integer> for Integer {
    #[inline]
    fn mul_assign(&mut self, other: &Integer) {
        self.0 *= &other.0;
    }
}

impl Add for Integer {
    type Output = Integer;

    #[inline]
    fn add(self, other: Integer) -> Self::Output {
        Integer(self.0 + other.0)
    }
}

impl Add<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn add(self, other: Integer) -> Self::Output {
        Integer(&self.0 + other.0)
    }
}

impl Add<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn add(self, other: &Integer) -> Self::Output {
        Integer(self.0 + &other.0)
    }
}

impl Add<&Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn add(self, other: &Integer) -> Self::Output {
        Integer(&self.0 + &other.0)
    }
}

impl AddAssign<i64> for Integer {
    #[inline]
    fn add_assign(&mut self, other: i64) {
        self.0 += other;
    }
}

impl AddAssign<&Integer> for Integer {
    #[inline]
    fn add_assign(&mut self, other: &Integer) {
        self.0 += &other.0;
    }
}

impl Div for Integer {
    type Output = Integer;

    #[inline]
    fn div(self, other: Integer) -> Integer {
        Integer(self.0 / other.0)
    }
}

impl Div<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn div(self, other: &Integer) -> Integer {
        Integer(self.0 / &other.0)
    }
}

impl Div<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn div(self, other: Integer) -> Integer {
        Integer(&self.0 / &other.0)
    }
}

impl Shr<u32> for Integer {
    type Output = Integer;

    #[inline]
    fn shr(self, rhs: u32) -> Self::Output {
        Integer(self.0 >> rhs as usize)
    }
}

impl Shr<u32> for &Integer {
    type Output = Integer;

    #[inline]
    fn shr(self, rhs: u32) -> Self::Output {
        Integer(&self.0 >> rhs as usize)
    }
}

impl ShrAssign<u32> for Integer {
    #[inline]
    fn shr_assign(&mut self, rhs: u32) {
        self.0 >>= rhs as usize;
    }
}

impl Shl<u32> for Integer {
    type Output = Integer;

    #[inline]
    fn shl(self, rhs: u32) -> Self::Output {
        Integer(self.0 << rhs as usize)
    }
}

impl Shl<u32> for &Integer {
    type Output = Integer;

    #[inline]
    fn shl(self, rhs: u32) -> Self::Output {
        Integer(&self.0 << rhs as usize)
    }
}

impl Not for Integer {
    type Output = Integer;

    #[inline]
    fn not(self) -> Self::Output {
        Integer(!self.0)
    }
}

impl Not for &Integer {
    type Output = Integer;

    #[inline]
    fn not(self) -> Self::Output {
        Integer(!&self.0)
    }
}

impl Rem for Integer {
    type Output = Integer;

    #[inline]
    fn rem(self, other: Integer) -> Self::Output {
        Integer(self.0.mod_floor(&other.0))
    }
}

impl Rem<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn rem(self, other: &Integer) -> Self::Output {
        Integer(self.0.mod_floor(&other.0))
    }
}

impl Rem<&Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn rem(self, other: &Integer) -> Self::Output {
        Integer(self.0.mod_floor(&other.0))
    }
}

impl Rem<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn rem(self, other: Integer) -> Self::Output {
        Integer(self.0.mod_floor(&other.0))
    }
}

impl BitAnd for Integer {
    type Output = Integer;

    #[inline]
    fn bitand(self, other: Integer) -> Self::Output {
        Integer(self.0 & &other.0)
    }
}

impl BitAnd<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn bitand(self, other: &Integer) -> Self::Output {
        Integer(self.0 & &other.0)
    }
}

impl BitAnd<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn bitand(self, other: Integer) -> Self::Output {
        Integer(&self.0 & other.0)
    }
}

impl BitAnd for &Integer {
    type Output = Integer;

    #[inline]
    fn bitand(self, other: &Integer) -> Self::Output {
        Integer(&self.0 & &other.0)
    }
}

impl BitOr for Integer {
    type Output = Integer;

    #[inline]
    fn bitor(self, other: Integer) -> Self::Output {
        Integer(self.0 | other.0)
    }
}

impl BitOr<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn bitor(self, other: &Integer) -> Self::Output {
        Integer(self.0 | &other.0)
    }
}

impl BitOr<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn bitor(self, other: Integer) -> Self::Output {
        Integer(&self.0 | other.0)
    }
}

impl BitOr for &Integer {
    type Output = Integer;

    #[inline]
    fn bitor(self, other: &Integer) -> Self::Output {
        Integer(&self.0 | &other.0)
    }
}

impl BitXor for Integer {
    type Output = Integer;

    #[inline]
    fn bitxor(self, other: Integer) -> Self::Output {
        Integer(self.0 ^ other.0)
    }
}

impl BitXor<&Integer> for Integer {
    type Output = Integer;

    #[inline]
    fn bitxor(self, other: &Integer) -> Self::Output {
        Integer(self.0 ^ &other.0)
    }
}

impl BitXor<Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn bitxor(self, other: Integer) -> Self::Output {
        Integer(&self.0 ^ other.0)
    }
}

impl BitXor<&Integer> for &Integer {
    type Output = Integer;

    #[inline]
    fn bitxor(self, other: &Integer) -> Self::Output {
        Integer(&self.0 ^ &other.0)
    }
}

impl PartialEq<i32> for Integer {
    #[inline]
    fn eq(&self, other: &i32) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialEq<i64> for Integer {
    #[inline]
    fn eq(&self, other: &i64) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialEq<isize> for Integer {
    #[inline]
    fn eq(&self, other: &isize) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialEq<usize> for Integer {
    #[inline]
    fn eq(&self, other: &usize) -> bool {
        self.0 == BigInt::from(*other)
    }
}

impl PartialEq<Integer> for isize {
    #[inline]
    fn eq(&self, other: &Integer) -> bool {
        other.0 == BigInt::from(*self)
    }
}

impl PartialOrd<i32> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &i32) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

impl PartialOrd<i64> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

impl PartialOrd<isize> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &isize) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

impl PartialOrd<usize> for Integer {
    #[inline]
    fn partial_cmp(&self, other: &usize) -> Option<Ordering> {
        self.0.partial_cmp(&BigInt::from(*other))
    }
}

impl FromStr for Integer {
    type Err = <BigInt as FromStr>::Err;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Integer(s.parse()?))
    }
}

impl Neg for Integer {
    type Output = Integer;

    #[inline]
    fn neg(self) -> Self {
        Integer(-self.0)
    }
}

impl Display for Integer {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

// Rational

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Rational(BigRational);

impl Rational {
    #[inline]
    pub fn new() -> Self {
        Rational(BigRational::from(BigInt::default()))
    }

    #[inline]
    pub fn from_f64(v: f64) -> Option<Self> {
        BigRational::from_f64(v).map(Rational)
    }

    #[inline]
    pub fn to_f64(&self) -> f64 {
        self.0.numer().to_f64().unwrap() / self.0.denom().to_f64().unwrap()
    }

    #[inline]
    pub fn numer(&self) -> &Integer {
        unsafe { ::std::mem::transmute(self.0.numer()) }
    }

    #[inline]
    pub fn denom(&self) -> &Integer {
        unsafe { ::std::mem::transmute(self.0.denom()) }
    }

    #[inline]
    pub fn abs(self) -> Self {
        Rational(self.0.abs())
    }

    #[inline]
    pub fn abs_ref(&self) -> Self {
        Rational(self.0.abs())
    }

    #[inline]
    pub fn fract_floor_ref(&self) -> &Self {
        panic!()
    }
}

impl From<isize> for Rational {
    #[inline]
    fn from(s: isize) -> Self {
        Rational(BigRational::new_raw(BigInt::from(s), One::one()))
    }
}

impl From<&Integer> for Rational {
    #[inline]
    fn from(s: &Integer) -> Self {
        Rational::from(s.clone())
    }
}

impl From<&Rational> for Rational {
    #[inline]
    fn from(s: &Rational) -> Self {
        s.clone()
    }
}

impl From<Integer> for Rational {
    #[inline]
    fn from(i: Integer) -> Self {
        Rational(BigRational::from(i.0))
    }
}

impl Add for Rational {
    type Output = Rational;

    #[inline]
    fn add(self, other: Rational) -> Self::Output {
        Rational(self.0 + other.0)
    }
}

impl Add<&Rational> for Rational {
    type Output = Rational;

    #[inline]
    fn add(self, other: &Rational) -> Self::Output {
        Rational(self.0 + &other.0)
    }
}

impl PartialEq<i32> for Rational {
    #[inline]
    fn eq(&self, other: &i32) -> bool {
        self.0 == BigRational::from(BigInt::from(*other))
    }
}

impl PartialEq<i64> for Rational {
    #[inline]
    fn eq(&self, other: &i64) -> bool {
        self.0 == BigRational::from(BigInt::from(*other))
    }
}

impl PartialEq<isize> for Rational {
    #[inline]
    fn eq(&self, other: &isize) -> bool {
        self == &Rational::from(*other)
    }
}

impl PartialEq<Rational> for isize {
    #[inline]
    fn eq(&self, other: &Rational) -> bool {
        other == &Rational::from(*self)
    }
}

impl PartialOrd<isize> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &isize) -> Option<Ordering> {
        self.0.partial_cmp(&BigRational::from(BigInt::from(*other)))
    }
}

impl PartialOrd<i64> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        self.0.partial_cmp(&BigRational::from(BigInt::from(*other)))
    }
}

impl PartialOrd<i32> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &i32) -> Option<Ordering> {
        self.0.partial_cmp(&BigRational::from(BigInt::from(*other)))
    }
}

impl Neg for Rational {
    type Output = Rational;

    #[inline]
    fn neg(self) -> Self {
        Rational(-self.0)
    }
}

impl Mul for Rational {
    type Output = Rational;

    #[inline]
    fn mul(self, other: Rational) -> Self::Output {
        Rational(self.0 * other.0)
    }
}

impl Mul<&Rational> for Rational {
    type Output = Rational;

    fn mul(self, other: &Rational) -> Self::Output {
        Rational(self.0 * &other.0)
    }
}

impl Div for Rational {
    type Output = Rational;

    #[inline]
    fn div(self, other: Rational) -> Self::Output {
        Rational(self.0 / other.0)
    }
}

impl Div<&Rational> for &Rational {
    type Output = Rational;

    #[inline]
    fn div(self, other: &Rational) -> Self::Output {
        Rational(&self.0 / &other.0)
    }
}

impl Display for Rational {
    #[inline]
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub trait Assign<Src = Self> {
    fn assign(&mut self, src: Src);
}

impl Assign<&Rational> for (&mut Rational, &mut Integer) {
    fn assign(&mut self, _src: &Rational) {
        panic!()
    }
}

pub mod ops {
    use super::{Integer, Rational};

    pub trait Pow<Rhs> {
        type Output;
        fn pow(self, rhs: Rhs) -> Self::Output;
    }

    impl Pow<u32> for Integer {
        type Output = Integer;

        fn pow(self, rhs: u32) -> Self::Output {
            Integer(num_traits::Pow::pow(&self.0, rhs))
        }
    }

    pub trait PowAssign<Rhs> {
        fn pow_assign(&mut self, rhs: Rhs);
    }

    impl PowAssign<u32> for Integer {
        fn pow_assign(&mut self, rhs: u32) {
            // FIXME: make it efficient
            self.0 = num_traits::Pow::pow(&self.0, rhs);
        }
    }

    pub trait NegAssign {
        fn neg_assign(&mut self);
    }

    impl NegAssign for Integer {
        fn neg_assign(&mut self) {
            self.0 = -std::mem::replace(self, Integer::new()).0;
        }
    }

    impl NegAssign for Rational {
        #[inline]
        fn neg_assign(&mut self) {
            self.0 = -std::mem::replace(self, Rational::new()).0;
        }
    }
}

pub mod rand {
    use super::Integer;
    use std::marker::PhantomData;

    pub struct RandState<'a>{
        _marker: PhantomData<&'a ()>,
    }

    impl<'a> RandState<'a> {
        pub fn new() -> Self {
            unsafe { libc::srand(libc::time(std::ptr::null_mut()) as _) };
            RandState { _marker: PhantomData }
        }

        pub fn borrow_mut(&self) -> &Self {
            self
        }

        pub fn bits(&mut self, bits: u32) -> u32 {
            assert!(bits <= 32);
            (unsafe { libc::rand() } as u32) & (u32::max_value() >> (32 - bits))
        }

        pub fn seed(&mut self, seed: &Integer) {
            unsafe { libc::srand(seed.to_f64() as _)}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::ops::NegAssign;

    #[test]
    fn bits() {
        let mut rand = rand::RandState::new();
        for bits in 1..32 {
            for _ in 0..100 {
                let r = rand.bits(bits);
                let max = 1 << bits;
                assert!(max > r, "{} > {}", max, r);
            }
        }
    }

    #[test]
    fn neg_rational() {
        let mut x = Rational::from_f64(5.0).unwrap();
        let x_neg = Rational::from_f64(-5.0).unwrap();
        x.neg_assign();
        assert_eq!(x, x_neg);
    }

    #[test]
    fn neg_integer() {
        let mut x = Integer::from(5);
        let x_neg = Integer::from(-5);
        x.neg_assign();
        assert_eq!(x, x_neg);
    }
}
