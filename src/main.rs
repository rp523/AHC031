#![allow(unused_macros, unused_imports, dead_code)]
use permutohedron::LexicalPermutation;
use std::any::TypeId;
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::mem::swap;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};

macro_rules! __debug_impl {
    ($x:expr) => {
        eprint!("{}={}  ", stringify!($x), &$x);
    };
    ($x:expr, $($y:expr),+) => (
        __debug_impl!($x);
        __debug_impl!($($y),+);
    );
}
macro_rules! __debug_line {
    () => {
        eprint!("L{}  ", line!());
    };
}
macro_rules! __debug_select {
    () => {
        eprintln!();
    };
    ($x:expr) => {
        __debug_line!();
        __debug_impl!($x);
        eprintln!();
    };
    ($x:expr, $($y:expr),+) => (
        __debug_line!();
        __debug_impl!($x);
        __debug_impl!($($y),+);
        eprintln!();
    );
}
macro_rules! debug {
    () => {
        if cfg!(debug_assertions) {
            __debug_select!();
        }
    };
    ($($xs:expr),+) => {
        if cfg!(debug_assertions) {
            __debug_select!($($xs),+);
        }
    };
}

pub trait Identity {
    fn identity() -> Self;
}
impl Identity for i32 {
    fn identity() -> Self {
        1_i32
    }
}
impl Identity for u32 {
    fn identity() -> Self {
        1_u32
    }
}
impl Identity for i64 {
    fn identity() -> Self {
        1_i64
    }
}
impl Identity for u64 {
    fn identity() -> Self {
        1_u64
    }
}
impl Identity for i128 {
    fn identity() -> Self {
        1_i128
    }
}
impl Identity for u128 {
    fn identity() -> Self {
        1_u128
    }
}
impl Identity for f64 {
    fn identity() -> Self {
        1_f64
    }
}
impl Identity for usize {
    fn identity() -> Self {
        1_usize
    }
}

mod change_min_max {
    pub trait ChangeMinMax<T> {
        fn chmin(&mut self, rhs: T) -> bool;
        fn chmax(&mut self, rhs: T) -> bool;
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for T {
        fn chmin(&mut self, rhs: T) -> bool {
            if *self > rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
        fn chmax(&mut self, rhs: T) -> bool {
            if *self < rhs {
                *self = rhs;
                true
            } else {
                false
            }
        }
    }
    impl<T: PartialOrd + Copy> ChangeMinMax<T> for Option<T> {
        fn chmin(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val > rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
        fn chmax(&mut self, rhs: T) -> bool {
            if let Some(val) = *self {
                if val < rhs {
                    *self = Some(rhs);
                    true
                } else {
                    false
                }
            } else {
                *self = Some(rhs);
                true
            }
        }
    }
}
use change_min_max::ChangeMinMax;

mod gcd {
    use std::cmp::{PartialEq, PartialOrd};
    use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign};
    pub fn gcd<T: Copy + Sub<Output = T> + Rem<Output = T> + PartialEq>(a: T, b: T) -> T {
        #[allow(clippy::eq_op)]
        let zero = a - a;
        if b == zero {
            a
        } else {
            gcd(b, a % b)
        }
    }
    // returns (p, q) s. t. ap + bq = gcd(a, b)
    pub fn ext_gcd<
        T: Eq
            + Copy
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>,
    >(
        a: T,
        b: T,
    ) -> (T, T) {
        #[allow(clippy::eq_op)]
        let zero = b - b;
        #[allow(clippy::eq_op)]
        let one = b / b;
        if a == zero {
            return (zero, one);
        }
        // (b % a) * x + a * y = gcd(a, b)
        // b % a = b - (b / a) * a
        // ->
        // (b - (b / a) * a) * x + a * y = gcd(a, b)
        // a * (y - (b / a) * x) + b * x = gcd(a, b)
        let (x, y) = ext_gcd(b % a, a);
        (y - b / a * x, x)
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(m1, m2), x) s.t. x = r1 (mod  m1) and x = r2 (mod m2)
    fn chinese_rem_elem2<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign,
    >(
        m1: T,
        r1: T,
        m2: T,
        r2: T,
    ) -> Option<(T, T)> {
        #[allow(clippy::eq_op)]
        let zero = m1 - m1;
        #[allow(clippy::eq_op)]
        let one = m1 / m1;
        let (p, _q) = ext_gcd(m1, m2);
        let g = gcd(m1, m2);
        if (r2 - r1) % g != zero {
            None
        } else {
            let lcm = m1 * (m2 / g);
            let mut r = r1 + m1 * ((r2 - r1) / g) * p;
            if r < zero {
                let dv = (-r + lcm - one) / lcm;
                r += dv * lcm;
            }
            r %= lcm;
            Some((lcm, r))
        }
    }
    // Chinese Remainder Theorem
    // when exists, returns (lcm(mods), x) s.t. x = r_i (mod  m_i) for all i.
    pub fn chinese_rem<
        T: Eq
            + Copy
            + Neg<Output = T>
            + PartialOrd
            + Add<Output = T>
            + AddAssign
            + Sub<Output = T>
            + SubAssign
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + RemAssign,
    >(
        mods: &[T],
        rems: &[T],
    ) -> Option<(T, T)> {
        debug_assert!(mods.len() == rems.len());
        #[allow(clippy::eq_op)]
        let zero = mods[0] - mods[0];
        #[allow(clippy::eq_op)]
        let one = mods[0] / mods[0];
        let mut lcm = one;
        let mut rem = zero;
        for (m, r) in mods.iter().copied().zip(rems.iter().copied()) {
            if let Some((nlcm, nrem)) = chinese_rem_elem2(lcm, rem, m, r) {
                lcm = nlcm;
                rem = nrem;
            } else {
                return None;
            }
        }
        Some((lcm, rem))
    }
}
use gcd::*;

fn factorial_impl<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T>,
>(
    p: usize,
    memo: &mut Vec<usize>,
    update_op: fn(T, T) -> T,
) -> T {
    while memo.len() < 2_usize {
        memo.push(1_usize);
    }
    while memo.len() <= p + 1 {
        let last_val: T = T::from(*memo.last().unwrap());
        memo.push(update_op(last_val, T::from(memo.len())).into());
    }
    T::from(memo[p])
}

fn factorial<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x * y) }
}

fn factorial_inv<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    p: usize,
) -> T {
    static mut MEMO: Vec<usize> = Vec::<usize>::new();
    unsafe { factorial_impl(p, &mut MEMO, |x: T, y: T| x / y) }
}

fn combination<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if n < k {
        return T::from(0_usize);
    }
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return (T::from(n) * T::from(n - 1)) / T::from(2);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(k) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / (factorial::<T>(k) * factorial::<T>(n - k))
    }
}

fn combination_with_overlap<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    combination(n + k - 1, k)
}

fn permutation<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::from(1_usize);
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return T::from(n) * T::from(n - 1);
    }

    if TypeId::of::<mint>() == TypeId::of::<T>() {
        factorial::<T>(n) * factorial_inv::<T>(n - k)
    } else {
        factorial::<T>(n) / factorial::<T>(n - k)
    }
}

mod union_find {
    #[derive(Debug, Clone)]
    pub struct UnionFind {
        pub graph: Vec<Vec<usize>>,
        parents: Vec<usize>,
        grp_sz: Vec<usize>,
        grp_num: usize,
    }

    impl UnionFind {
        pub fn new(sz: usize) -> Self {
            Self {
                graph: vec![vec![]; sz],
                parents: (0..sz).collect::<Vec<usize>>(),
                grp_sz: vec![1; sz],
                grp_num: sz,
            }
        }
        pub fn root(&mut self, v: usize) -> usize {
            if v == self.parents[v] {
                v
            } else {
                self.parents[v] = self.root(self.parents[v]);
                self.parents[v]
            }
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.root(a) == self.root(b)
        }
        pub fn unite(&mut self, into: usize, from: usize) {
            self.graph[into].push(from);
            self.graph[from].push(into);
            let r_into = self.root(into);
            let r_from = self.root(from);
            if r_into != r_from {
                self.parents[r_from] = r_into;
                self.grp_sz[r_into] += self.grp_sz[r_from];
                self.grp_sz[r_from] = 0;
                self.grp_num -= 1;
            }
        }
        pub fn group_num(&self) -> usize {
            self.grp_num
        }
        pub fn group_size(&mut self, a: usize) -> usize {
            let ra = self.root(a);
            self.grp_sz[ra]
        }
    }
}
use union_find::UnionFind;

mod segment_tree {
    use std::ops::{Add, Sub};
    #[derive(Debug, Clone)]
    pub struct SegmentTree<T> {
        n2: usize,   // implemented leaf num (2^n)
        neff: usize, // effective vector length
        dat: Vec<T>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Clone> SegmentTree<T> {
        pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut s = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_val.clone(); 2 * n2 - 1],
            };

            for i in 0..n {
                s.set(i, ini_val.clone());
            }
            s
        }
        pub fn from_vec(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
            let n = ini_values.len();
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut st = Self {
                n2,
                neff: n,
                pair_op,
                dat: vec![ini_values[0].clone(); 2 * n2 - 1],
            };

            for (i, ini_val) in ini_values.iter().enumerate() {
                st.set(i, ini_val.clone());
            }
            st
        }
        pub fn set(&mut self, mut pos: usize, val: T) {
            pos += self.n2 - 1;
            self.dat[pos] = val;
            while pos > 0 {
                pos = (pos - 1) / 2; // parent
                self.dat[pos] =
                    (self.pair_op)(self.dat[pos * 2 + 1].clone(), self.dat[pos * 2 + 2].clone());
            }
        }
        pub fn get(&self, pos: usize) -> T {
            self.dat[pos + self.n2 - 1].clone()
        }
        // get query value of [a, b]
        pub fn query(&self, a: usize, b: usize) -> T {
            self.query_sub(a, b + 1, 0, 0, self.n2)
        }
        // get query value of [a, b)
        fn query_sub(&self, a: usize, b: usize, node: usize, node_l: usize, node_r: usize) -> T {
            if (node_r <= a) || (b <= node_l) {
                panic!("invalid query range, ({a}, {b})");
            } else if (a <= node_l) && (node_r <= b) {
                // this not is covered by given interval.
                self.dat[node].clone()
            } else if a < (node_l + node_r) / 2 {
                let vl = self.query_sub(a, b, node * 2 + 1, node_l, (node_l + node_r) / 2);
                if (node_l + node_r) / 2 < b {
                    let vr = self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r);
                    (self.pair_op)(vl, vr)
                } else {
                    vl
                }
            } else if (node_l + node_r) / 2 < b {
                self.query_sub(a, b, node * 2 + 2, (node_l + node_r) / 2, node_r)
            } else {
                panic!("invalid query range, ({a}, {b})");
            }
        }
    }
    impl<T: Copy + Add<Output = T> + Sub<Output = T>> SegmentTree<T> {
        pub fn add(&mut self, pos: usize, add_val: T) {
            self.set(pos, self.get(pos) + add_val);
        }
        pub fn sub(&mut self, pos: usize, sub_val: T) {
            self.set(pos, self.get(pos) - sub_val);
        }
    }
}
use segment_tree::SegmentTree;

mod lazy_segment_tree {
    #[derive(Clone)]
    pub struct LazySegmentTree<X, M> {
        // https://algo-logic.info/segment-tree/#toc_id_3
        n2: usize,                    // num of node(integer power of 2)
        pair_op: fn(X, X) -> X,       // node_val x node_val -> node_val
        update_op: fn(X, M) -> X,     // node_val x update_val -> node
        update_concat: fn(M, M) -> M, // update_val x update_val -> update_val
        dat: Vec<X>,                  // node values
        lazy_ops: Vec<Option<M>>,     // reserved operations
        built: bool,
    }
    impl<X: Clone, M: Clone> LazySegmentTree<X, M> {
        pub fn new(
            n: usize,
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            ini_val: X,
        ) -> Self {
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![ini_val.clone(); n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            ret.init_all(ini_val);
            ret
        }
        pub fn from_vec(
            pair_op: fn(X, X) -> X,
            update_op: fn(X, M) -> X,
            update_concat: fn(M, M) -> M,
            init_vals: Vec<X>,
        ) -> Self {
            let n = init_vals.len();
            let mut n2 = 1_usize;
            while n > n2 {
                n2 *= 2;
            }
            let mut ret = Self {
                n2,
                pair_op,
                update_op,
                update_concat,
                dat: vec![init_vals[0].clone(); n * 4],
                lazy_ops: vec![None; n * 4],
                built: false,
            };
            for (i, init_val) in init_vals.iter().enumerate() {
                ret.set(i, init_val.clone());
            }
            ret
        }
        pub fn query(&mut self, a: usize, b: usize) -> X // closed interval
        {
            self.query_sub(a, b + 1, 0, 0, self.n2) // half_open interval
        }
        pub fn reserve(&mut self, a: usize, b: usize, m: M) // closed interval
        {
            self.reserve_sub(a, b + 1, m, 0, 0, self.n2); // half_open interval
        }
        pub fn set(&mut self, i: usize, val: X) {
            self.dat[i + self.n2 - 1] = val;
        }
        fn init_all(&mut self, ini_val: X) {
            for i in 0..self.n2 {
                self.set(i, ini_val.clone());
            }
        }
        fn build(&mut self) {
            for k in (0..self.n2).rev().skip(1) {
                self.dat[k] =
                    (self.pair_op)(self.dat[2 * k + 1].clone(), self.dat[2 * k + 2].clone());
            }
        }
        fn lazy_eval(&mut self, node: usize) {
            if !self.built {
                self.build();
                self.built = true;
            }
            if let Some(lazy_val) = self.lazy_ops[node].clone() {
                if node < self.n2 - 1 {
                    // if the target node is not a terminal one, propagate to its' children.
                    for d in 1..=2_usize {
                        let nc = node * 2 + d;
                        if let Some(nc_lazy_val) = self.lazy_ops[nc].clone() {
                            self.lazy_ops[nc] =
                                Some((self.update_concat)(nc_lazy_val, lazy_val.clone()));
                        } else {
                            self.lazy_ops[nc] = Some(lazy_val.clone());
                        }
                    }
                }
                // update the target node
                self.dat[node] = (self.update_op)(self.dat[node].clone(), lazy_val);
                self.lazy_ops[node] = None;
            }
        }
        fn reserve_sub(
            &mut self,
            a: usize,
            b: usize,
            m: M,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // this node is inside the query range.
                if let Some(lazy_val) = self.lazy_ops[node].clone() {
                    self.lazy_ops[node] = Some((self.update_concat)(lazy_val, m));
                } else {
                    self.lazy_ops[node] = Some(m);
                }
                self.lazy_eval(node);
            } else if (node_r > a) && (b > node_l) {
                // this node and query range overlap partly.
                self.reserve_sub(a, b, m.clone(), node * 2 + 1, node_l, (node_l + node_r) / 2); // 左の子
                self.reserve_sub(a, b, m, node * 2 + 2, (node_l + node_r) / 2, node_r); // 右の子
                self.dat[node] = (self.pair_op)(
                    self.dat[node * 2 + 1].clone(),
                    self.dat[node * 2 + 2].clone(),
                );
            }
        }
        fn query_sub(
            &mut self,
            a: usize,
            b: usize,
            node: usize,
            node_l: usize,
            node_r: usize,
        ) -> X {
            self.lazy_eval(node);
            if (a <= node_l) && (node_r <= b) {
                // this node is inside the query range.
                self.dat[node].clone()
            } else if (node_r > a) && (b > node_l) {
                // this node and query range overlap partly.
                let n0 = node * 2 + 1;
                let l0 = node_l;
                let r0 = (node_l + node_r) / 2;
                let n1 = node * 2 + 2;
                let l1 = (node_l + node_r) / 2;
                let r1 = node_r;
                if (a < r0) && (l0 < b) {
                    if (a < r1) && (l1 < b) {
                        (self.pair_op)(
                            self.query_sub(a, b, n0, l0, r0),
                            self.query_sub(a, b, n1, l1, r1),
                        )
                    } else {
                        self.query_sub(a, b, n0, l0, r0)
                    }
                } else if (a < r1) && (l1 < b) {
                    self.query_sub(a, b, n1, l1, r1)
                } else {
                    panic!("invalid arg range {}, {}", a, b);
                }
            } else {
                panic!(
                    "this node and query range have no common area, {}, {}",
                    a, b
                );
            }
        }
    }
}
use lazy_segment_tree::LazySegmentTree;

mod modint {
    use crate::gcd::ext_gcd;
    use crate::Identity;
    use i64 as mtype;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};
    static mut MOD: mtype = 2;

    #[derive(Clone, Copy, Eq, Hash, PartialEq)]
    pub struct ModInt {
        x: mtype,
    }
    impl ModInt {
        pub fn set_mod(val: mtype) {
            unsafe {
                MOD = val;
            }
        }
        pub fn get_mod() -> mtype {
            unsafe { MOD }
        }
        pub fn val(&self) -> mtype {
            self.x
        }
        fn new(mut sig: mtype) -> Self {
            if sig < 0 {
                let ab = (-sig + Self::get_mod() - 1) / Self::get_mod();
                sig += ab * Self::get_mod();
                debug_assert!(sig >= 0);
            }
            Self {
                x: sig % Self::get_mod(),
            }
        }
        fn inverse(&self) -> Self {
            // x * inv_x + M * _ = 1 (mod M)
            Self::new(ext_gcd(self.x, Self::get_mod()).0)

            // [Fermat's little theorem]
            // if p is prime, for any integer a, a^p = a (mod p)
            // especially when a and b is coprime, a^(p-1) = 1 (mod p).
            // -> inverse of a is a^(p-2).

            //let mut ret = Self { x: 1 };
            //let mut mul: Self = *self;
            //let mut p = Self::get_mod() - 2;
            //while p > 0 {
            //    if p & 1 != 0 {
            //        ret *= mul;
            //    }
            //    p >>= 1;
            //    mul *= mul;
            //}
            //ret
        }
        pub fn pow(self, mut p: usize) -> Self {
            let mut ret = ModInt::from(1);
            let mut mul = self;
            while p > 0 {
                if p & 1 != 0 {
                    ret *= mul;
                }
                p >>= 1;
                mul *= mul;
            }
            ret
        }
    }
    impl Identity for ModInt {
        fn identity() -> Self {
            Self { x: 1 }
        }
    }
    impl AddAssign<Self> for ModInt {
        fn add_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x + rhs.x);
        }
    }
    impl AddAssign<i64> for ModInt {
        fn add_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x + rhs);
        }
    }
    impl AddAssign<i32> for ModInt {
        fn add_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x + rhs as i64);
        }
    }
    impl AddAssign<usize> for ModInt {
        fn add_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x + rhs as i64);
        }
    }
    impl Add<ModInt> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x + rhs.x)
        }
    }
    impl Add<i64> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x + rhs)
        }
    }
    impl Add<i32> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x + rhs as i64)
        }
    }
    impl Add<usize> for ModInt {
        type Output = ModInt;
        fn add(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x + rhs as i64)
        }
    }
    impl Add<ModInt> for i64 {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self + rhs.x)
        }
    }
    impl Add<ModInt> for i32 {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 + rhs.x)
        }
    }
    impl Add<ModInt> for usize {
        type Output = ModInt;
        fn add(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 + rhs.x)
        }
    }
    impl SubAssign<Self> for ModInt {
        fn sub_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x - rhs.x);
        }
    }
    impl SubAssign<i64> for ModInt {
        fn sub_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x - rhs);
        }
    }
    impl SubAssign<i32> for ModInt {
        fn sub_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x - rhs as i64);
        }
    }
    impl SubAssign<usize> for ModInt {
        fn sub_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x - rhs as i64);
        }
    }
    impl Sub<ModInt> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x - rhs.x)
        }
    }
    impl Sub<i64> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x - rhs)
        }
    }
    impl Sub<i32> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x - rhs as i64)
        }
    }
    impl Sub<usize> for ModInt {
        type Output = ModInt;
        fn sub(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x - rhs as i64)
        }
    }
    impl Sub<ModInt> for i64 {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self - rhs.x)
        }
    }
    impl Sub<ModInt> for i32 {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 - rhs.x)
        }
    }
    impl Sub<ModInt> for usize {
        type Output = ModInt;
        fn sub(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 - rhs.x)
        }
    }
    impl MulAssign<Self> for ModInt {
        fn mul_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x * rhs.x);
        }
    }
    impl MulAssign<i64> for ModInt {
        fn mul_assign(&mut self, rhs: i64) {
            *self = ModInt::new(self.x * rhs);
        }
    }
    impl MulAssign<i32> for ModInt {
        fn mul_assign(&mut self, rhs: i32) {
            *self = ModInt::new(self.x * rhs as i64);
        }
    }
    impl MulAssign<usize> for ModInt {
        fn mul_assign(&mut self, rhs: usize) {
            *self = ModInt::new(self.x * rhs as i64);
        }
    }
    impl Mul<ModInt> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x * rhs.x)
        }
    }
    impl Mul<i64> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: i64) -> Self::Output {
            ModInt::new(self.x * rhs)
        }
    }
    impl Mul<i32> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: i32) -> Self::Output {
            ModInt::new(self.x * rhs as i64)
        }
    }
    impl Mul<usize> for ModInt {
        type Output = ModInt;
        fn mul(self, rhs: usize) -> Self::Output {
            ModInt::new(self.x * rhs as i64)
        }
    }
    impl Mul<ModInt> for i64 {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self * rhs.x)
        }
    }
    impl Mul<ModInt> for i32 {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 * rhs.x)
        }
    }
    impl Mul<ModInt> for usize {
        type Output = ModInt;
        fn mul(self, rhs: ModInt) -> Self::Output {
            ModInt::new(self as i64 * rhs.x)
        }
    }
    impl DivAssign<Self> for ModInt {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
    impl DivAssign<i64> for ModInt {
        fn div_assign(&mut self, rhs: i64) {
            *self = *self / ModInt::new(rhs);
        }
    }
    impl DivAssign<i32> for ModInt {
        fn div_assign(&mut self, rhs: i32) {
            *self = *self / ModInt::new(rhs as i64);
        }
    }
    impl DivAssign<usize> for ModInt {
        fn div_assign(&mut self, rhs: usize) {
            *self = *self / ModInt::new(rhs as i64);
        }
    }
    impl Div<ModInt> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * rhs.inverse().x)
        }
    }
    impl Div<i64> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: i64) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs).inverse().x)
        }
    }
    impl Div<i32> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: i32) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs as i64).inverse().x)
        }
    }
    impl Div<usize> for ModInt {
        type Output = ModInt;
        fn div(self, rhs: usize) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * ModInt::new(rhs as i64).inverse().x)
        }
    }
    impl Div<ModInt> for i64 {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self * rhs.inverse().x)
        }
    }
    impl Div<ModInt> for i32 {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self as i64 * rhs.inverse().x)
        }
    }
    impl Div<ModInt> for usize {
        type Output = ModInt;
        fn div(self, rhs: ModInt) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self as i64 * rhs.inverse().x)
        }
    }
    impl From<usize> for ModInt {
        fn from(x: usize) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl From<i64> for ModInt {
        fn from(x: i64) -> Self {
            ModInt::new(x)
        }
    }
    impl From<i32> for ModInt {
        fn from(x: i32) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl std::str::FromStr for ModInt {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s.parse::<i64>() {
                Ok(x) => Ok(ModInt::from(x)),
                Err(e) => Err(e),
            }
        }
    }
    impl std::iter::Sum for ModInt {
        fn sum<I: Iterator<Item = ModInt>>(iter: I) -> Self {
            let mut ret = ModInt::new(0);
            for v in iter {
                ret += v;
            }
            ret
        }
    }
    #[allow(clippy::from_over_into)]
    impl Into<usize> for ModInt {
        fn into(self) -> usize {
            self.x as usize
        }
    }
    impl fmt::Display for ModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
    impl fmt::Debug for ModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
}
use modint::ModInt as mint;

fn precalc_power(base: i64, n: usize) -> Vec<mint> {
    let mut ret = vec![mint::from(1); n + 1];
    for p in 1..=n {
        ret[p] = ret[p - 1] * base;
    }
    ret
}

fn precalc_invpower(base: i64, n: usize) -> Vec<mint> {
    let mut ret = vec![mint::from(1); n + 1];
    let inv_base = mint::from(1) / base;
    for p in 1..=n {
        ret[p] = ret[p - 1] * inv_base;
    }
    ret
}

pub trait IntegerOperation {
    fn into_primes(self) -> BTreeMap<Self, usize>
    where
        Self: Sized;
    fn into_divisors(self) -> Vec<Self>
    where
        Self: Sized;
    fn squared_length(&self, rhs: Self) -> Self;
}
impl<
        T: Copy
            + Ord
            + AddAssign
            + SubAssign
            + MulAssign
            + DivAssign
            + Add<Output = T>
            + Sub<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>,
    > IntegerOperation for T
{
    fn into_primes(self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
    {
        #[allow(clippy::eq_op)]
        let zero = self - self;
        if self == zero {
            panic!("Zero has no divisors.");
        }
        #[allow(clippy::eq_op)]
        let one = self / self;
        let two = one + one;
        let three = two + one;
        let mut n = self;
        let mut ans = BTreeMap::new();
        while n % two == zero {
            *ans.entry(two).or_insert(0) += 1;
            n /= two;
        }
        {
            let mut i = three;
            while i * i <= n {
                while n % i == zero {
                    *ans.entry(i).or_insert(0) += 1;
                    n /= i;
                }
                i += two;
            }
        }
        if n != one {
            *ans.entry(n).or_insert(0) += 1;
        }
        ans
    }
    fn into_divisors(self) -> Vec<T> // O(N^0.5)
    {
        #[allow(clippy::eq_op)]
        let zero = self - self;
        if self == zero {
            panic!("Zero has no primes.");
        }
        #[allow(clippy::eq_op)]
        let one = self / self;
        let n = self;
        let mut ret: Vec<T> = Vec::new();
        {
            let mut i = one;
            while i * i <= n {
                if n % i == zero {
                    ret.push(i);
                    if i * i != n {
                        ret.push(n / i);
                    }
                }
                i += one;
            }
        }
        ret.sort();
        ret
    }
    fn squared_length(&self, rhs: Self) -> Self {
        *self * *self + rhs * rhs
    }
}

pub trait CoordinateCompress<T> {
    fn compress_encoder(&self) -> HashMap<T, usize>;
    fn compress_decoder(&self) -> Vec<T>;
    fn compress(self) -> Vec<usize>;
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for Vec<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for BTreeSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = HashMap::new();
        for (i, &key) in self.iter().enumerate() {
            dict.insert(key, i);
        }
        dict
    }
    fn compress_decoder(&self) -> Vec<T> {
        self.iter().copied().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        (0..self.len()).collect::<Vec<usize>>()
    }
}
impl<T: Copy + Ord + std::hash::Hash> CoordinateCompress<T> for HashSet<T> {
    fn compress_encoder(&self) -> HashMap<T, usize> {
        let mut dict = BTreeSet::new();
        for &x in self.iter() {
            dict.insert(x);
        }
        let mut ret = HashMap::new();
        for (i, value) in dict.into_iter().enumerate() {
            ret.insert(value, i);
        }
        ret
    }
    fn compress_decoder(&self) -> Vec<T> {
        let mut keys = BTreeSet::<T>::new();
        for &x in self.iter() {
            keys.insert(x);
        }
        keys.into_iter().collect::<Vec<T>>()
    }
    fn compress(self) -> Vec<usize> {
        let dict = self.compress_encoder();
        self.into_iter().map(|x| dict[&x]).collect::<Vec<usize>>()
    }
}

mod xor_shift_64 {
    pub struct XorShift64(u64);
    impl XorShift64 {
        pub fn new() -> Self {
            XorShift64(88172645463325252_u64)
        }
        pub fn next_f64(&mut self) -> f64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0 as f64 * 5.421_010_862_427_522e-20
        }
        pub fn next_u64(&mut self) -> u64 {
            self.0 = self.0 ^ (self.0 << 7);
            self.0 = self.0 ^ (self.0 >> 9);
            self.0
        }
        pub fn next_usize(&mut self) -> usize {
            self.next_u64() as usize
        }
    }
}
use xor_shift_64::XorShift64;

mod rooted_tree {
    use std::mem::swap;

    use crate::union_find::UnionFind;
    pub struct RootedTree {
        n: usize,
        doubling_bit_width: usize,
        root: usize,
        rise_tbl: Vec<Vec<Option<usize>>>,
        dist: Vec<Option<i64>>,
        step: Vec<Option<usize>>,
        pub graph: Vec<Vec<(i64, usize)>>,
        edge_cnt: usize,
        uf: UnionFind,
    }
    impl RootedTree {
        pub fn new(n: usize, root: usize) -> RootedTree {
            let mut doubling_bit_width = 1;
            while (1 << doubling_bit_width) < n {
                doubling_bit_width += 1;
            }
            RootedTree {
                n,
                doubling_bit_width,
                root,
                rise_tbl: vec![vec![None; n]; doubling_bit_width],
                dist: vec![None; n],
                step: vec![None; n],
                graph: vec![vec![]; n],
                edge_cnt: 0,
                uf: UnionFind::new(n),
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) {
            self.unite_with_distance(a, b, 1);
        }
        pub fn unite_with_distance(&mut self, a: usize, b: usize, delta: i64) {
            self.graph[a].push((delta, b));
            self.graph[b].push((delta, a));
            self.edge_cnt += 1;
            self.uf.unite(a, b);
            if self.edge_cnt >= self.n - 1 {
                if self.uf.group_num() != 1 {
                    panic!("nodes are NOT connected into one union.")
                }
                self.analyze(self.root);
            }
        }
        pub fn stepback(&self, from: usize, step: usize) -> usize {
            let mut v = from;
            for d in (0..self.doubling_bit_width - 1).rev() {
                if ((step >> d) & 1) != 0 {
                    v = self.rise_tbl[d][v].unwrap();
                }
            }
            v
        }
        fn dfs(
            v: usize,
            pre: Option<usize>,
            graph: &Vec<Vec<(i64, usize)>>,
            dist: &mut Vec<Option<i64>>,
            step: &mut Vec<Option<usize>>,
            rise_tbl: &mut Vec<Vec<Option<usize>>>,
        ) {
            for (delta, nv) in graph[v].iter() {
                if let Some(pre) = pre {
                    if *nv == pre {
                        continue;
                    }
                }
                if dist[*nv].is_none() {
                    dist[*nv] = Some(dist[v].unwrap() + *delta);
                    step[*nv] = Some(step[v].unwrap() + 1);
                    rise_tbl[0][*nv] = Some(v);
                    Self::dfs(*nv, Some(v), graph, dist, step, rise_tbl);
                }
            }
        }
        fn analyze(&mut self, root: usize) {
            self.dist[root] = Some(0);
            self.step[root] = Some(0);
            self.rise_tbl[0][root] = Some(root);
            Self::dfs(
                root,
                None,
                &self.graph,
                &mut self.dist,
                &mut self.step,
                &mut self.rise_tbl,
            );
            // doubling
            for d in (0..self.doubling_bit_width).skip(1) {
                for v in 0_usize..self.n {
                    self.rise_tbl[d][v] = self.rise_tbl[d - 1][self.rise_tbl[d - 1][v].unwrap()];
                }
            }
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            if self.step[a] > self.step[b] {
                swap(&mut a, &mut b);
            }
            assert!(self.step[a] <= self.step[b]);
            // bring up the deeper one to the same level of the shallower one.
            for d in (0..self.doubling_bit_width).rev() {
                let rise_v = self.rise_tbl[d][b].unwrap();
                if self.step[rise_v] >= self.step[a] {
                    b = rise_v;
                }
            }
            assert!(self.step[a] == self.step[b]);
            if a != b {
                // simultaneously rise to the previous level of LCA.
                for d in (0..self.doubling_bit_width).rev() {
                    if self.rise_tbl[d][a] != self.rise_tbl[d][b] {
                        a = self.rise_tbl[d][a].unwrap();
                        b = self.rise_tbl[d][b].unwrap();
                    }
                }
                // 1-step higher level is LCA.
                a = self.rise_tbl[0][a].unwrap();
                b = self.rise_tbl[0][b].unwrap();
            }
            assert!(a == b);
            a
        }
        pub fn distance(&self, a: usize, b: usize) -> i64 {
            let lca_v = self.lca(a, b);
            self.dist[a].unwrap() + self.dist[b].unwrap() - 2 * self.dist[lca_v].unwrap()
        }
    }
}
use rooted_tree::RootedTree;

mod btree_map_binary_search {
    use std::collections::BTreeMap;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeMapBinarySearch<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn greater_than(&self, key: &K) -> Option<(&K, &V)>;
        fn less_equal(&self, key: &K) -> Option<(&K, &V)>;
        fn less_than(&self, key: &K) -> Option<(&K, &V)>;
    }
    impl<K: Ord, V> BTreeMapBinarySearch<K, V> for BTreeMap<K, V> {
        fn greater_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &K) -> Option<(&K, &V)> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_map_binary_search::BTreeMapBinarySearch;

mod btree_set_binary_search {
    use std::collections::BTreeSet;
    use std::ops::Bound::{Excluded, Included, Unbounded};
    pub trait BTreeSetBinarySearch<T> {
        fn greater_equal(&self, key: &T) -> Option<&T>;
        fn greater_than(&self, key: &T) -> Option<&T>;
        fn less_equal(&self, key: &T) -> Option<&T>;
        fn less_than(&self, key: &T) -> Option<&T>;
    }
    impl<T: Ord> BTreeSetBinarySearch<T> for BTreeSet<T> {
        fn greater_equal(&self, key: &T) -> Option<&T> {
            self.range((Included(key), Unbounded)).next()
        }
        fn greater_than(&self, key: &T) -> Option<&T> {
            self.range((Excluded(key), Unbounded)).next()
        }
        fn less_equal(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Included(key))).next_back()
        }
        fn less_than(&self, key: &T) -> Option<&T> {
            self.range((Unbounded, Excluded(key))).next_back()
        }
    }
}
use btree_set_binary_search::BTreeSetBinarySearch;

mod sort_vec_binary_search {
    static mut VEC_IS_SORTED_ONCE: bool = false;
    #[allow(clippy::type_complexity)]
    fn sorted_binary_search<'a, T: PartialOrd>(
        vec: &'a Vec<T>,
        key: &T,
        earlier: fn(&T, &T) -> bool,
    ) -> (Option<(usize, &'a T)>, Option<(usize, &'a T)>) {
        unsafe {
            if !VEC_IS_SORTED_ONCE {
                for i in 1..vec.len() {
                    assert!(vec[i - 1] <= vec[i]);
                }
                VEC_IS_SORTED_ONCE = true;
            }
        }
        if vec.is_empty() {
            return (None, None);
        }

        if !earlier(&vec[0], key) {
            (None, Some((0, &vec[0])))
        } else if earlier(vec.last().unwrap(), key) {
            (Some((vec.len() - 1, &vec[vec.len() - 1])), None)
        } else {
            let mut l = 0;
            let mut r = vec.len() - 1;
            while r - l > 1 {
                let m = (l + r) / 2;
                if earlier(&vec[m], key) {
                    l = m;
                } else {
                    r = m;
                }
            }
            (Some((l, &vec[l])), Some((r, &vec[r])))
        }
    }
    pub trait SortVecBinarySearch<T> {
        #[allow(clippy::type_complexity)]
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn greater_than(&self, key: &T) -> Option<(usize, &T)>;
        fn less_equal(&self, key: &T) -> Option<(usize, &T)>;
        fn less_than(&self, key: &T) -> Option<(usize, &T)>;
    }
    impl<T: Ord> SortVecBinarySearch<T> for Vec<T> {
        fn greater_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).1
        }
        fn greater_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).1
        }
        fn less_equal(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x <= y).0
        }
        fn less_than(&self, key: &T) -> Option<(usize, &T)> {
            sorted_binary_search(self, key, |x: &T, y: &T| x < y).0
        }
    }
}
use sort_vec_binary_search::SortVecBinarySearch;

mod map_counter {
    use std::cmp::Ord;
    use std::collections::{BTreeMap, HashMap};
    use std::hash::Hash;
    pub trait MapCounter<T> {
        fn incr(&mut self, key: T);
        fn incr_by(&mut self, key: T, delta: usize);
        fn decr(&mut self, key: &T);
        fn decr_by(&mut self, key: &T, delta: usize);
    }
    impl<T: Ord + Clone> MapCounter<T> for BTreeMap<T, usize> {
        fn incr(&mut self, key: T) {
            self.incr_by(key, 1);
        }
        fn incr_by(&mut self, key: T, delta: usize) {
            *self.entry(key).or_insert(0) += delta;
        }
        fn decr(&mut self, key: &T) {
            self.decr_by(key, 1);
        }
        fn decr_by(&mut self, key: &T, delta: usize) {
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
        }
    }
    impl<T: Clone + Hash + Eq> MapCounter<T> for HashMap<T, usize> {
        fn incr(&mut self, key: T) {
            self.incr_by(key, 1);
        }
        fn incr_by(&mut self, key: T, delta: usize) {
            *self.entry(key).or_insert(0) += delta;
        }
        fn decr(&mut self, key: &T) {
            self.decr_by(key, 1);
        }
        fn decr_by(&mut self, key: &T, delta: usize) {
            let v = self.entry(key.clone()).or_insert(0);
            debug_assert!(*v >= delta);
            *v -= delta;
            if *v == 0 {
                self.remove(key);
            }
        }
    }
}
use map_counter::MapCounter;

#[derive(Debug, Clone, Copy, Eq, Hash, PartialEq)]
struct Line2d(i64, i64, i64);
impl Line2d {
    // identify line from 2 differemt point
    fn new(y0: i64, x0: i64, y1: i64, x1: i64) -> Line2d {
        let mut b = y1 - y0;
        let mut a = x1 - x0;
        let mut c = x1 * y0 - x0 * y1;
        let r = gcd(a.abs(), gcd(b.abs(), c.abs()));
        a /= r;
        b /= r;
        c /= r;
        if (a == 0) && (b < 0) {
            a = -a;
            b = -b;
            c = -c;
        }
        if a < 0 {
            a = -a;
            b = -b;
            c = -c;
        }
        Line2d(a, b, c)
    }
}

mod strongly_connected_component {
    pub struct StronglyConnectedComponent {
        n: usize,
        pub graph: Vec<Vec<usize>>,
        bwd_graph: Vec<Vec<usize>>,
    }
    impl StronglyConnectedComponent {
        pub fn new(n: usize) -> StronglyConnectedComponent {
            StronglyConnectedComponent {
                n,
                graph: vec![vec![]; n],
                bwd_graph: vec![vec![]; n],
            }
        }
        pub fn add(&mut self, from: usize, into: usize) {
            self.graph[from].push(into);
            self.bwd_graph[into].push(from);
        }
        pub fn decompose(&mut self) -> Vec<Vec<usize>> {
            let mut scc = Vec::<Vec<usize>>::new();
            let mut fwd_seen = vec![false; self.n];
            let mut order = Vec::<usize>::new();
            for i in 0..self.n {
                if !fwd_seen[i] {
                    StronglyConnectedComponent::fwd_dfs(
                        &self.graph,
                        i,
                        None,
                        &mut fwd_seen,
                        &mut order,
                    );
                }
            }
            order.reverse();
            let mut bwd_seen = vec![false; self.n];
            for i_ in &order {
                let i = *i_;
                if !bwd_seen[i] {
                    let mut grp = Vec::<usize>::new();
                    StronglyConnectedComponent::bwd_dfs(
                        &self.bwd_graph,
                        i,
                        None,
                        &mut bwd_seen,
                        &mut grp,
                    );
                    grp.reverse();
                    scc.push(grp);
                }
            }
            scc
        }
        fn bwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            grp: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::bwd_dfs(graph, nv, Some(v), seen, grp);
                }
            }
            grp.push(v);
        }
        fn fwd_dfs(
            graph: &Vec<Vec<usize>>,
            v: usize,
            pre: Option<usize>,
            seen: &mut Vec<bool>,
            order: &mut Vec<usize>,
        ) {
            seen[v] = true;
            for nv_ in &graph[v] {
                let nv = *nv_;
                if let Some(pre_v) = pre {
                    if nv == pre_v {
                        continue;
                    }
                }
                if !seen[nv] {
                    StronglyConnectedComponent::fwd_dfs(graph, nv, Some(v), seen, order);
                }
            }
            order.push(v);
        }
    }
}
use strongly_connected_component::StronglyConnectedComponent as Scc;

mod pair {
    use std::ops::{Add, AddAssign, Sub, SubAssign};
    #[derive(Debug, Clone, Copy)]
    pub struct Pair<X, Y> {
        pub x: X,
        pub y: Y,
    }
    impl<X: AddAssign, Y: AddAssign> AddAssign for Pair<X, Y> {
        fn add_assign(&mut self, rhs: Self) {
            self.x += rhs.x;
            self.y += rhs.y;
        }
    }
    impl<X: Add<Output = X>, Y: Add<Output = Y>> Add for Pair<X, Y> {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                x: self.x + rhs.x,
                y: self.y + rhs.y,
            }
        }
    }
    impl<X: SubAssign, Y: SubAssign> SubAssign for Pair<X, Y> {
        fn sub_assign(&mut self, rhs: Self) {
            self.x -= rhs.x;
            self.y -= rhs.y;
        }
    }
    impl<X: Sub<Output = X>, Y: Sub<Output = Y>> Sub for Pair<X, Y> {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                x: self.x - rhs.x,
                y: self.y - rhs.y,
            }
        }
    }
}
use pair::Pair;

mod usize_move_delta {
    pub trait MoveDelta<T> {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize>;
    }
    impl<T: Copy + Into<i64>> MoveDelta<T> for usize {
        fn move_delta(self, delta: T, lim_lo: usize, lim_hi: usize) -> Option<usize> {
            let delta: i64 = delta.into();
            let added: i64 = self as i64 + delta;
            let lim_lo: i64 = lim_lo as i64;
            let lim_hi: i64 = lim_hi as i64;
            if (lim_lo <= added) && (added <= lim_hi) {
                Some(added as usize)
            } else {
                None
            }
        }
    }
}
use usize_move_delta::MoveDelta;

fn exit_by<T: std::fmt::Display>(msg: T) {
    println!("{}", msg);
    std::process::exit(0);
}

pub struct PermutationIterator<T> {
    v: Vec<T>,
    is_first: bool,
}
impl<T: Copy + Ord + Clone> PermutationIterator<T> {
    pub fn new(mut v: Vec<T>) -> PermutationIterator<T> {
        v.sort();
        PermutationIterator { v, is_first: true }
    }
}
impl<T: Copy + Ord + Clone> Iterator for PermutationIterator<T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.is_first {
            self.is_first = false;
            Some(self.v.clone())
        } else if self.v.next_permutation() {
            Some(self.v.clone())
        } else {
            None
        }
    }
}

pub trait IntoPermutations<T: Copy + Ord + Clone> {
    fn into_permutations(self) -> PermutationIterator<T>;
}
// implement for ones that has IntoIterator.
impl<T: Copy + Ord + Clone, I: IntoIterator<Item = T>> IntoPermutations<T> for I {
    fn into_permutations(self) -> PermutationIterator<T> {
        PermutationIterator::new(self.into_iter().collect())
    }
}
mod add_header {
    pub trait AddHeader<T> {
        fn add_header(&mut self, add_val: T);
    }
    impl<T> AddHeader<T> for Vec<T>
    where
        Vec<T>: Clone,
    {
        fn add_header(&mut self, add_val: T) {
            let cpy = self.clone();
            self.clear();
            self.push(add_val);
            for cpy_val in cpy {
                self.push(cpy_val);
            }
        }
    }
}
use add_header::AddHeader;

mod auto_sort_vec {
    use crate::segment_tree::SegmentTree;
    pub struct AutoSortVec {
        max_val: usize,
        st: SegmentTree<usize>,
    }
    impl AutoSortVec {
        pub fn new(max_val: usize) -> AutoSortVec {
            AutoSortVec {
                max_val,
                st: SegmentTree::<usize>::new(max_val + 1, |x, y| x + y, 0),
            }
        }
        pub fn len(&self) -> usize {
            self.st.query(0, self.max_val)
        }
        pub fn push(&mut self, val: usize) {
            self.st.add(val, 1);
        }
        pub fn remove_value(&mut self, val: usize) {
            self.st.sub(val, 1);
        }
        pub fn value_to_index(&self, val: usize) -> usize {
            if val == 0 {
                0
            } else {
                self.st.query(0, val - 1)
            }
        }
        pub fn at(&self, idx: usize) -> usize {
            let idx1 = idx + 1;
            if self.st.get(0) >= idx1 {
                0
            } else if self.st.query(0, self.max_val - 1) < idx1 {
                self.max_val
            } else {
                let mut l = 0;
                let mut r = self.max_val;
                while r - l > 1 {
                    let m = (r + l) / 2;
                    let sm = self.st.query(0, m);
                    if sm < idx1 {
                        l = m;
                    } else {
                        r = m;
                    }
                }
                r
            }
        }
    }
}
use auto_sort_vec::AutoSortVec;

mod my_string {
    use std::ops::{Index, IndexMut};
    use std::slice::SliceIndex;
    #[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Hash)]
    pub struct Str {
        vc: Vec<char>,
    }
    impl Str {
        pub fn new() -> Self {
            Self { vc: vec![] }
        }
        pub fn from(s: &str) -> Self {
            Self {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            }
        }
        pub fn len(&self) -> usize {
            self.vc.len()
        }
        pub fn clear(&mut self) {
            self.vc.clear()
        }
        pub fn is_empty(&self) -> bool {
            self.vc.is_empty()
        }
        pub fn first(&self) -> Option<&char> {
            self.vc.first()
        }
        pub fn last(&self) -> Option<&char> {
            self.vc.last()
        }
        pub fn push(&mut self, c: char) {
            self.vc.push(c);
        }
        pub fn push_str(&mut self, s: &str) {
            for c in s.to_string().chars().collect::<Vec<char>>().into_iter() {
                self.push(c);
            }
        }
        pub fn pop(&mut self) -> Option<char> {
            self.vc.pop()
        }
        pub fn into_iter(self) -> std::vec::IntoIter<char> {
            self.vc.into_iter()
        }
        pub fn iter(&self) -> std::slice::Iter<char> {
            self.vc.iter()
        }
        pub fn iter_mut(&mut self) -> std::slice::IterMut<char> {
            self.vc.iter_mut()
        }
        pub fn swap(&mut self, a: usize, b: usize) {
            self.vc.swap(a, b);
        }
        pub fn reverse(&mut self) {
            self.vc.reverse();
        }
        pub fn find(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.find(&p)
        }
        pub fn rfind(&self, p: &Str) -> Option<usize> {
            let s: String = self.vc.iter().collect::<String>();
            let p: String = p.vc.iter().collect::<String>();
            s.rfind(&p)
        }
        pub fn into_values(self, base: char) -> Vec<usize> {
            self.vc
                .into_iter()
                .map(|c| (c as u8 - base as u8) as usize)
                .collect::<Vec<usize>>()
        }
        pub fn sort(&mut self) {
            self.vc.sort();
        }
        pub fn remove(&mut self, index: usize) -> char {
            self.vc.remove(index)
        }
    }
    impl std::str::FromStr for Str {
        type Err = ();
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            Ok(Str {
                vc: s.to_string().chars().collect::<Vec<char>>(),
            })
        }
    }
    impl<Idx: SliceIndex<[char]>> Index<Idx> for Str {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vc[i]
        }
    }
    impl<Idx: SliceIndex<[char]>> IndexMut<Idx> for Str {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vc[index]
        }
    }
    impl std::ops::Add<Str> for Str {
        type Output = Str;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            for c in rhs.into_iter() {
                ret.vc.push(c);
            }
            ret
        }
    }
    impl std::ops::AddAssign<Str> for Str {
        fn add_assign(&mut self, rhs: Self) {
            for c in rhs.into_iter() {
                self.vc.push(c);
            }
        }
    }
    impl std::ops::Add<char> for Str {
        type Output = Str;
        fn add(self, rhs: char) -> Self::Output {
            let mut ret = self;
            ret.vc.push(rhs);
            ret
        }
    }
    impl std::ops::AddAssign<char> for Str {
        fn add_assign(&mut self, rhs: char) {
            self.vc.push(rhs);
        }
    }
    impl std::fmt::Display for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
    impl std::fmt::Debug for Str {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{}", self.vc.iter().collect::<String>())
        }
    }
}
use my_string::Str;

mod rolling_hash {
    use u64 as htype;
    const MODS: [htype; 2] = [1000000007, 998244353];
    pub struct RollingHash {
        cum_hashes: Vec<Vec<htype>>,
        base: usize,
        base_powers: Vec<Vec<htype>>,
        base_powers_inv: Vec<Vec<htype>>,
    }
    pub struct RollingHashValue<'a> {
        org: &'a RollingHash,
        i0: usize,
        i1: usize,
    }
    pub trait GenRollingHash {
        fn rolling_hash(&self, base: usize) -> RollingHash;
    }
    impl GenRollingHash for Vec<usize> {
        fn rolling_hash(&self, base: usize) -> RollingHash {
            RollingHash::new(self, base)
        }
    }
    impl RollingHash {
        pub fn new(values: &Vec<usize>, base: usize) -> RollingHash {
            let n = values.len();

            let mut base_powers = vec![vec![1; n]; 2];
            for m in 0..2 {
                for p in 1..n {
                    base_powers[m][p] = (base_powers[m][p - 1] * base as htype) % MODS[m];
                }
            }

            let calc_inv_base = |md: u64, base: htype| -> htype {
                let mut p = md - 2;
                let mut ret: htype = 1;
                let mut mul = base;
                while p > 0 {
                    if p & 1 != 0 {
                        ret = (ret * mul) % md;
                    }
                    p >>= 1;
                    mul = (mul * mul) % md;
                }
                ret
            };
            let inv_bases = (0..2)
                .map(|m| calc_inv_base(MODS[m], base as htype))
                .collect::<Vec<_>>();

            let mut base_powers_inv = vec![vec![1; n]; 2];
            for m in 0..2 {
                for p in 1..n {
                    base_powers_inv[m][p] = (base_powers_inv[m][p - 1] * inv_bases[m]) % MODS[m];
                }
            }

            let mut cum_hashes = (0..2)
                .map(|m| {
                    (0..n)
                        .map(|i| (values[i] as htype * base_powers[m][i]) % MODS[m])
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<Vec<_>>>();

            for m in 0..2 {
                for i in 1..n {
                    cum_hashes[m][i] += cum_hashes[m][i - 1];
                    cum_hashes[m][i] %= MODS[m];
                }
            }

            Self {
                cum_hashes,
                base,
                base_powers,
                base_powers_inv,
            }
        }
        // hash value of array range (closed interval, [i0, i1])
        pub fn hash(&self, i0: usize, i1: usize) -> RollingHashValue {
            RollingHashValue { org: self, i0, i1 }
        }
    }
    impl<'a> RollingHashValue<'a> {
        fn get(&'a self) -> (htype, htype) {
            let retv = if self.i0 > 0 {
                (0..2)
                    .map(|m| {
                        ((MODS[m] + self.org.cum_hashes[m][self.i1]
                            - self.org.cum_hashes[m][self.i0 - 1])
                            * self.org.base_powers_inv[m][self.i0])
                            % MODS[m]
                    })
                    .collect::<Vec<_>>()
            } else {
                (0..2)
                    .map(|m| self.org.cum_hashes[m][self.i1])
                    .collect::<Vec<_>>()
            };
            (retv[0], retv[1])
        }
    }
    impl PartialEq for RollingHashValue<'_> {
        fn eq(&self, other: &Self) -> bool {
            debug_assert!(self.i1 - self.i0 == other.i1 - other.i0);
            self.get() == other.get()
        }
    }
}
use rolling_hash::*;

mod rational {
    use crate::gcd::gcd;
    use std::cmp::Ordering;
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Rational {
        pub num: i64,
        pub denom: i64,
    }
    impl Rational {
        pub fn new(num: i64, denom: i64) -> Self {
            if num == 0 {
                if denom == 0 {
                    panic!("0/0 is indefinite.")
                } else {
                    Self { num: 0, denom: 1 }
                }
            } else if denom == 0 {
                Self { num: 1, denom: 0 }
            } else {
                let (num, denom) = {
                    if denom < 0 {
                        (-num, -denom)
                    } else {
                        (num, denom)
                    }
                };
                let g = gcd(num.abs(), denom.abs());
                debug_assert!(denom >= 0);
                Self {
                    num: num / g,
                    denom: denom / g,
                }
            }
        }
    }
    impl AddAssign<Self> for Rational {
        fn add_assign(&mut self, rhs: Self) {
            let d0 = self.denom.abs();
            let d1 = rhs.denom.abs();
            let denom = d0 * (d1 / gcd(d0, d1));
            let n0 = self.num * (denom / d0);
            let n1 = rhs.num * (denom / d1);
            *self = Self::new(n0 + n1, denom);
        }
    }
    impl Add<Self> for Rational {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret += rhs;
            ret
        }
    }
    impl SubAssign<Self> for Rational {
        fn sub_assign(&mut self, rhs: Self) {
            *self += Self::new(-rhs.num, rhs.denom);
        }
    }
    impl Sub<Self> for Rational {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret -= rhs;
            ret
        }
    }
    impl MulAssign<Self> for Rational {
        fn mul_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.num, self.denom * rhs.denom);
        }
    }
    impl Mul<Self> for Rational {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret *= rhs;
            ret
        }
    }
    impl DivAssign<Self> for Rational {
        fn div_assign(&mut self, rhs: Self) {
            *self = Self::new(self.num * rhs.denom, rhs.num * self.denom);
        }
    }
    impl Div<Self> for Rational {
        type Output = Self;
        fn div(self, rhs: Self) -> Self::Output {
            let mut ret = self;
            ret /= rhs;
            ret
        }
    }
    impl Neg for Rational {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self::new(-self.num, self.denom)
        }
    }
    impl PartialOrd for Rational {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            i64::partial_cmp(&(self.num * other.denom), &(self.denom * other.num))
        }
    }
    impl Ord for Rational {
        fn cmp(&self, other: &Self) -> Ordering {
            Self::partial_cmp(self, other).unwrap()
        }
    }
    impl fmt::Display for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
    impl fmt::Debug for Rational {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.num as f64 / self.denom as f64)
        }
    }
}
use rational::Rational;

fn z_algo(s: &[usize]) -> Vec<usize> {
    // https://www.youtube.com/watch?v=f6ct5PQHqM0
    let n = s.len();
    let mut last_match = None;
    let mut ret = vec![0; n];
    ret[0] = n;
    for i in 1..n {
        let mut match_delta = 0;
        if let Some((m0, m1)) = last_match {
            if i < m1 {
                // reuse calculated info.
                if i + ret[i - m0] != m1 {
                    // built from old one, and finish.
                    ret[i] = min(ret[i - m0], m1 - i);
                    continue;
                } else {
                    // skip known range, and continues.
                    match_delta = m1 - i;
                }
            }
        }
        // expand until unmatch is found.
        while i + match_delta < n {
            if s[match_delta] == s[i + match_delta] {
                match_delta += 1;
            } else {
                break;
            }
        }
        // set header-match lentgh.
        ret[i] = match_delta;
        // update last match range for future use.
        if let Some((_m0, m1)) = last_match {
            if i + match_delta <= m1 {
                continue;
            }
        }
        last_match = Some((i, i + match_delta));
    }
    ret
}

fn convex_hull<
    T: Copy
        + PartialOrd<T>
        + Add<Output = T>
        + Sub<Output = T>
        + Div<Output = T>
        + Add<Output = T>
        + Sub<Output = T>
        + Mul<Output = T>,
>(
    points: &[(T, T)],
) -> Vec<(T, T)> {
    fn outer_product<T: Copy + Add<Output = T> + Sub<Output = T> + Mul<Output = T>>(
        origin: (T, T),
        end0: (T, T),
        end1: (T, T),
    ) -> T {
        (end0.0 - origin.0) * (end1.1 - origin.1) - (end0.1 - origin.1) * (end1.0 - origin.0)
    }

    #[allow(clippy::eq_op)]
    let zero = points[0].0 - points[0].0;
    let mut points = points.to_vec();
    points.sort_by(|x, y| x.partial_cmp(y).unwrap());
    let mut ret = vec![];
    for &p in points.iter() {
        while ret.len() >= 2 {
            if outer_product(ret[ret.len() - 1], ret[ret.len() - 2], p) < zero {
                break;
            }
            ret.pop();
        }
        ret.push(p);
    }
    let t = ret.len();
    for p in points.into_iter().rev().skip(1) {
        while ret.len() > t {
            if outer_product(ret[ret.len() - 1], ret[ret.len() - 2], p) < zero {
                break;
            }
            ret.pop();
        }
        ret.push(p);
    }
    ret
}

mod matrix {
    use crate::Identity;
    use std::iter::Sum;
    use std::ops::{Add, Index, IndexMut, Mul, MulAssign, Sub};
    use std::slice::SliceIndex;
    #[derive(Clone)]
    pub struct Matrix<T> {
        h: usize,
        w: usize,
        vals: Vec<Vec<T>>,
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>> Matrix<T> {
        pub fn new(h: usize, w: usize) -> Self {
            let v1 = T::identity();
            #[allow(clippy::eq_op)]
            let v0 = v1 - v1;
            Self {
                h,
                w,
                vals: vec![vec![v0; w]; h],
            }
        }
        pub fn identity(h: usize, w: usize) -> Self {
            debug_assert!(h == w);
            let v1 = T::identity();
            #[allow(clippy::eq_op)]
            let v0 = v1 - v1;
            let mut vals = vec![vec![v0; w]; h];
            for (y, line) in vals.iter_mut().enumerate() {
                for (x, val) in line.iter_mut().enumerate() {
                    *val = if y == x { v1 } else { v0 };
                }
            }
            Self { h, w, vals }
        }
        pub fn pow(&self, mut p: usize) -> Self {
            let mut ret = Self::identity(self.h, self.w);
            let mut mul = self.clone();
            while p > 0 {
                if p & 1 != 0 {
                    ret = ret.clone() * mul.clone();
                }
                p >>= 1;
                mul = mul.clone() * mul.clone();
            }
            ret
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> Index<Idx> for Matrix<T> {
        type Output = Idx::Output;
        fn index(&self, i: Idx) -> &Self::Output {
            &self.vals[i]
        }
    }
    impl<T, Idx: SliceIndex<[Vec<T>]>> IndexMut<Idx> for Matrix<T> {
        fn index_mut(&mut self, index: Idx) -> &mut Self::Output {
            &mut self.vals[index]
        }
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>>
        Mul<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.w == rhs.h);
            let mut ret = Self::new(self.h, rhs.w);
            for y in 0..ret.h {
                for x in 0..ret.w {
                    ret[y][x] = (0..self.w).map(|i| self[y][i] * rhs[i][x]).sum::<T>();
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Vec<T>> for Matrix<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Vec<T>) -> Self::Output {
            debug_assert!(self.w == rhs.len());
            (0..self.h)
                .map(|y| (0..self.w).map(|x| self[y][x] * rhs[x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<T: Clone + Copy + Mul + Sum<<T as Mul>::Output>> Mul<Matrix<T>> for Vec<T> {
        type Output = Vec<T>;
        fn mul(self, rhs: Matrix<T>) -> Self::Output {
            debug_assert!(self.len() == rhs.h);
            (0..rhs.w)
                .map(|x| (0..rhs.h).map(|y| self[y] * rhs[y][x]).sum::<T>())
                .collect::<Vec<_>>()
        }
    }
    impl<
            T: Clone
                + Copy
                + Identity
                + Add<Output = T>
                + Sub<Output = T>
                + Mul
                + Sum<<T as Mul>::Output>,
        > Add<Matrix<T>> for Matrix<T>
    {
        type Output = Matrix<T>;
        fn add(self, rhs: Self) -> Self::Output {
            let mut ret = Matrix::<T>::new(self.h, self.w);
            for y in 0..self.h {
                for x in 0..self.w {
                    ret[y][x] = self[y][x] + rhs[y][x];
                }
            }
            ret
        }
    }
    impl<T: Clone + Copy + Identity + Sub<Output = T> + Mul + Sum<<T as Mul>::Output>>
        MulAssign<Matrix<T>> for Matrix<T>
    {
        fn mul_assign(&mut self, rhs: Matrix<T>) {
            *self = self.clone() * rhs;
        }
    }
}
use matrix::Matrix;

mod suffix_array {
    use crate::my_string;
    use crate::CoordinateCompress;
    use std::cmp::{min, Ord, Ordering};
    fn compare_sa(rank: &[i64], i: usize, j: usize, k: usize, n: usize) -> Ordering {
        if rank[i] != rank[j] {
            rank[i].cmp(&rank[j])
        } else {
            let ri = if i + k <= n { rank[i + k] } else { 0 };
            let rj = if j + k <= n { rank[j + k] } else { 0 };
            ri.cmp(&rj)
        }
    }
    fn construct_sa(s: &[usize]) -> Vec<usize> {
        let n = s.len();
        let mut sa = vec![0usize; n + 1];
        let mut rank = vec![0i64; n + 1];
        for i in 0..=n {
            sa[i] = i;
            rank[i] = if i < n { s[i] as i64 } else { -1 };
        }
        let mut nrank = rank.clone();
        let mut k = 1;
        while k <= n {
            sa.sort_by(|&i, &j| compare_sa(&rank, i, j, k, n));
            nrank[sa[0]] = 0;
            for i in 1..=n {
                nrank[sa[i]] = nrank[sa[i - 1]]
                    + if compare_sa(&rank, sa[i - 1], sa[i], k, n) == Ordering::Less {
                        1
                    } else {
                        0
                    };
            }
            std::mem::swap(&mut rank, &mut nrank);
            //
            k <<= 1;
        }
        sa.into_iter().skip(1).collect::<Vec<_>>()
    }
    pub trait ToSuffixArray {
        fn to_suffix_array(&self) -> Vec<usize>;
    }
    impl ToSuffixArray for Vec<usize> {
        fn to_suffix_array(&self) -> Vec<usize> {
            construct_sa(self)
        }
    }
}
use suffix_array::ToSuffixArray;

mod flow {
    use crate::change_min_max::ChangeMinMax;
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;
    #[derive(Clone, Copy)]
    pub struct Edge {
        pub to: usize,
        pub rev_idx: usize,  // index of paired edge at node "to".
        pub cap_remain: i64, // flow <= cap_remain
        pub flow: i64,       // flow can be negative.
        pub cost: i64,       // for min-cost flow
    }
    pub struct Flow {
        pub g: Vec<Vec<Edge>>,
        flow_lb_sum: i64,
        neg_cost_any: bool,
    }
    impl Flow {
        pub fn new(n: usize) -> Self {
            Self {
                g: vec![vec![]; n + 2],
                flow_lb_sum: 0,
                neg_cost_any: false,
            }
        }
        pub fn add_edge(&mut self, from: usize, to: usize, cap: i64) {
            self.add_cost_edge(from, to, cap, 0);
        }
        pub fn add_flowbound_edge(&mut self, from: usize, to: usize, cap_min: i64, cap_max: i64) {
            self.add_flowbound_cost_edge(from, to, cap_min, cap_max, 0);
        }
        pub fn add_flowbound_cost_edge(
            &mut self,
            from: usize,
            to: usize,
            cap_min: i64,
            cap_max: i64,
            cost: i64,
        ) {
            self.add_cost_edge(from, to, cap_max - cap_min, cost);
            if cap_min > 0 {
                self.flow_lb_sum += cap_min;
                let dummy_src = self.g.len() - 2;
                self.add_cost_edge(dummy_src, to, cap_min, cost);
                let dummy_dst = self.g.len() - 1;
                self.add_cost_edge(from, dummy_dst, cap_min, cost);
            }
        }
        pub fn add_cost_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
            let rev_idx = self.g[to].len();
            self.g[from].push(Edge {
                to,
                rev_idx,
                cap_remain: cap,
                flow: 0,
                cost,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                cap_remain: 0,
                flow: 0,
                cost: -cost,
            });
            if cost < 0 {
                self.neg_cost_any = true;
            }
        }
        fn bfs(g: &[Vec<Edge>], source: usize) -> Vec<Option<usize>> {
            let mut level = vec![None; g.len()];
            level[source] = Some(0);
            let mut que = std::collections::VecDeque::new();
            que.push_back(source);
            while let Some(v) = que.pop_front() {
                let nxt_level = level[v].unwrap() + 1;
                for edge in g[v].iter().copied() {
                    if level[edge.to].is_none() && (edge.cap_remain > edge.flow) {
                        level[edge.to] = Some(nxt_level);
                        que.push_back(edge.to);
                    }
                }
            }
            level
        }
        fn dfs(
            g: &mut [Vec<Edge>],
            v: usize,
            sink: usize,
            flow: i64,
            search_cnt: &mut [usize],
            level: &[Option<usize>],
        ) -> i64 {
            if v == sink {
                return flow;
            }
            while search_cnt[v] < g[v].len() {
                let (to, rev_idx, remain_capacity) = {
                    let edge = g[v][search_cnt[v]];
                    (edge.to, edge.rev_idx, edge.cap_remain - edge.flow)
                };
                if let Some(nxt_level) = level[to] {
                    if (level[v].unwrap() < nxt_level) && (remain_capacity > 0) {
                        let additional_flow = Self::dfs(
                            g,
                            to,
                            sink,
                            std::cmp::min(flow, remain_capacity),
                            search_cnt,
                            level,
                        );
                        if additional_flow > 0 {
                            g[v][search_cnt[v]].flow += additional_flow;
                            g[to][rev_idx].flow -= additional_flow;
                            return additional_flow;
                        }
                    }
                }
                search_cnt[v] += 1;
            }
            0
        }
        pub fn max_flow(&mut self, src: usize, dst: usize) -> Option<i64> {
            if self.flow_lb_sum == 0 {
                return Some(self.max_flow_impl(src, dst));
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            if self.max_flow_impl(dummy_src, dummy_dst) != self.flow_lb_sum {
                return None;
            }
            Some(self.max_flow_impl(src, dst))
        }
        fn max_flow_impl(&mut self, source: usize, sink: usize) -> i64 {
            let inf = 1i64 << 60;
            let mut flow = 0;
            loop {
                let level = Self::bfs(&self.g, source);
                if level[sink].is_none() {
                    break;
                }
                let mut search_cnt = vec![0; self.g.len()];
                loop {
                    let additional_flow =
                        Self::dfs(&mut self.g, source, sink, inf, &mut search_cnt, &level);
                    if additional_flow > 0 {
                        flow += additional_flow;
                    } else {
                        break;
                    }
                }
            }
            flow
        }
        pub fn min_cost_flow(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Option<(i64, i64)> {
            if self.flow_lb_sum == 0 {
                return self.min_cost_flow_impl(src, dst, flow_lb, flow_ub);
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            let (dcost, _ds_to_dt) =
                self.min_cost_flow_impl(dummy_src, dummy_dst, self.flow_lb_sum, self.flow_lb_sum)?;
            let (cost, s_to_t) = self.min_cost_flow_impl(src, dst, flow_lb, flow_ub)?;
            Some((cost + dcost, s_to_t))
        }
        fn min_cost_flow_impl(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Option<(i64, i64)> {
            if self.neg_cost_any {
                self.min_negcost_flow(src, dst, flow_lb, flow_ub)
            } else {
                self.min_poscost_flow(src, dst, flow_lb)
            }
        }
        fn min_negcost_flow(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Option<(i64, i64)> {
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            loop {
                dist[source] = Some(0);
                let mut update = true;
                while update {
                    update = false;
                    for (v, to) in self.g.iter().enumerate() {
                        if dist[v].is_none() {
                            continue;
                        }
                        for (ei, e) in to.iter().enumerate() {
                            if e.flow >= e.cap_remain {
                                continue;
                            }
                            let nd = dist[v].unwrap() + e.cost;
                            if dist[e.to].chmin(nd) {
                                prev[e.to] = Some((v, ei));
                                update = true;
                            }
                        }
                    }
                }

                if let Some(dist_sink) = dist[sink] {
                    if (flow_now >= flow_lb) && (dist_sink > 0) {
                        break;
                    }
                    let mut delta_flow = flow_ub - flow_now;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            let e = &self.g[pv][pei];
                            delta_flow.chmin(e.cap_remain - e.flow);
                            v = pv;
                        }
                    }
                    if delta_flow == 0 {
                        break;
                    }
                    flow_now += delta_flow;
                    min_cost += delta_flow * dist_sink;
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            self.g[pv][pei].flow += delta_flow;
                            let rev_idx = self.g[pv][pei].rev_idx;
                            self.g[v][rev_idx].flow -= delta_flow;
                            v = pv;
                        }
                    }
                } else if flow_now >= flow_lb {
                    break;
                } else {
                    return None;
                }

                dist.iter_mut().for_each(|x| *x = None);
                prev.iter_mut().for_each(|x| *x = None);
            }
            Some((min_cost, flow_now))
        }
        fn min_poscost_flow(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow;
        ) -> Option<(i64, i64)> {
            let mut flow_now = 0;
            let mut min_cost = 0;
            let mut h = vec![0; self.g.len()];
            let mut dist = vec![None; self.g.len()];
            let mut prev = vec![None; self.g.len()];
            while flow_now < flow_lb {
                let mut que = BinaryHeap::new();
                que.push((Reverse(0), source));
                dist[source] = Some(0);
                while let Some((Reverse(d), v)) = que.pop() {
                    if dist[v].unwrap() != d {
                        continue;
                    }
                    for (ei, e) in self.g[v].iter().enumerate() {
                        if e.flow >= e.cap_remain {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                dist[sink]?;
                h.iter_mut().zip(dist.iter()).for_each(|(h, d)| {
                    if let Some(d) = d {
                        *h += d
                    }
                });
                let mut delta_flow = flow_lb - flow_now;
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        let e = &self.g[pv][pei];
                        delta_flow.chmin(e.cap_remain - e.flow);
                        v = pv;
                    }
                }
                flow_now += delta_flow;
                min_cost += delta_flow * h[sink];
                {
                    let mut v = sink;
                    while let Some((pv, pei)) = prev[v] {
                        self.g[pv][pei].flow += delta_flow;
                        let rev_idx = self.g[pv][pei].rev_idx;
                        self.g[v][rev_idx].flow -= delta_flow;
                        v = pv;
                    }
                }

                dist.iter_mut().for_each(|dist| *dist = None);
                prev.iter_mut().for_each(|dist| *dist = None);
            }
            Some((min_cost, flow_now))
        }
    }
}
use flow::Flow;

mod convolution {
    // https://github.com/atcoder/ac-library/blob/master/atcoder/convolution.hpp
    use crate::{modint::ModInt as mint, IntegerOperation};
    pub fn convolution(arga: &[mint], argb: &[mint]) -> Vec<mint> {
        let n = arga.len();
        let m = argb.len();
        let z = 1 << ceil_pow2(n + m - 1);
        let mut a = vec![mint::from(0); z];
        let mut b = vec![mint::from(0); z];
        for (a, &arga) in a.iter_mut().zip(arga.iter()) {
            *a = arga;
        }
        butterfly(&mut a);
        for (b, &argb) in b.iter_mut().zip(argb.iter()) {
            *b = argb;
        }
        butterfly(&mut b);
        for (a, b) in a.iter_mut().zip(b.into_iter()) {
            *a *= b;
        }
        butterfly_inv(&mut a);
        while a.len() > n + m - 1 {
            a.pop();
        }
        let iz = mint::from(1) / mint::from(z);
        for a in a.iter_mut() {
            *a *= iz;
        }
        a
    }
    // returns 'r' s.t. 'r^(m - 1) == 1 (mod m)'
    fn primitive_root(m: i64) -> i64 {
        debug_assert!(is_prime(m));
        if m == 2 {
            return 1;
        }
        if m == 167772161 {
            return 3;
        }
        if m == 469762049 {
            return 3;
        }
        if m == 754974721 {
            return 11;
        }
        if m == 998244353 {
            return 3;
        }
        if m == 1000000007 {
            return 5;
        }
        let divs = ((m - 1) / 2).into_primes();

        for g in 2.. {
            let mut ok = true;
            for (&div, _) in divs.iter() {
                fn pow_mod(x: i64, mut p: i64, m: i64) -> i64 {
                    let mut ret = 1;
                    let mut mul = x % m;
                    while p > 0 {
                        if p & 1 != 0 {
                            ret *= mul;
                            ret %= m;
                        }
                        p >>= 1;
                        mul *= mul;
                        mul %= m;
                    }
                    ret
                }

                if pow_mod(g, (m - 1) / div, m) == 1 {
                    ok = false;
                    break;
                }
            }
            if ok {
                return g;
            }
        }
        unreachable!();
    }
    fn is_prime(x: i64) -> bool {
        if x == 1 {
            return false;
        }
        for i in 2.. {
            if i * i > x {
                return true;
            }
            if x % i == 0 {
                return false;
            }
        }
        unreachable!();
    }
    struct FFTinfo {
        root: Vec<mint>,  // root[i]^(2^i) == 1
        iroot: Vec<mint>, // root[i] * iroot[i] == 1
        rate2: Vec<mint>,
        irate2: Vec<mint>,
        rate3: Vec<mint>,
        irate3: Vec<mint>,
    }
    // returns minimum non-negative `x` s.t. `(n & (1 << x)) != 0`
    fn bsf(n: usize) -> usize {
        let mut x = 0;
        while (n & (1 << x)) == 0 {
            x += 1;
        }
        x
    }
    impl FFTinfo {
        fn new() -> Self {
            let rank2 = bsf((mint::get_mod() - 1) as usize);
            let mut root = vec![mint::from(0); rank2 + 1];
            let mut iroot = vec![mint::from(0); rank2 + 1];
            let mut rate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut irate2 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 2 + 1) as usize];
            let mut rate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];
            let mut irate3 = vec![mint::from(0); std::cmp::max(0, rank2 as i64 - 3 + 1) as usize];

            let g = primitive_root(mint::get_mod());
            root[rank2] = mint::from(g).pow((mint::get_mod() as usize - 1) >> rank2);
            iroot[rank2] = mint::from(1) / root[rank2];
            for i in (0..rank2).rev() {
                root[i] = root[i + 1] * root[i + 1];
                iroot[i] = iroot[i + 1] * iroot[i + 1];
            }

            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 2) {
                    rate2[i] = root[i + 2] * prod;
                    irate2[i] = iroot[i + 2] * iprod;
                    prod *= iroot[i + 2];
                    iprod *= root[i + 2];
                }
            }
            {
                let mut prod = mint::from(1);
                let mut iprod = mint::from(1);
                for i in 0..=(rank2 - 3) {
                    rate3[i] = root[i + 3] * prod;
                    irate3[i] = iroot[i + 3] * iprod;
                    prod *= iroot[i + 3];
                    iprod *= root[i + 3];
                }
            }

            Self {
                root,
                iroot,
                rate2,
                irate2,
                rate3,
                irate3,
            }
        }
    }
    fn ceil_pow2(n: usize) -> usize {
        let mut x = 0;
        while (1 << x) < n {
            x += 1;
        }
        x
    }
    fn butterfly(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = 0; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len < h {
            if h - len == 1 {
                let p = 1 << (h - len - 1);
                let mut rot = mint::from(1);
                for s in 0..(1 << len) {
                    let offset = s << (h - len);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p] * rot;
                        a[i + offset] = l + r;
                        a[i + offset + p] = l - r;
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate2[bsf(!s)];
                    }
                }
                len += 1;
            } else {
                // 4-base
                let p = 1 << (h - len - 2);
                let mut rot = mint::from(1);
                let imag = info.root[2];
                for s in 0..(1 << len) {
                    let rot2 = rot * rot;
                    let rot3 = rot2 * rot;
                    let offset = s << (h - len);
                    for i in 0..p {
                        let mod2 = mint::get_mod() * mint::get_mod();
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val() * rot.val();
                        let a2 = a[i + offset + 2 * p].val() * rot2.val();
                        let a3 = a[i + offset + 3 * p].val() * rot3.val();
                        let a1na3imag = mint::from(a1 + mod2 - a3).val() * imag.val();
                        let na2 = mod2 - a2;
                        a[i + offset] = mint::from(a0 + a2 + a1 + a3);
                        a[i + offset + p] = mint::from(a0 + a2 + (2 * mod2 - (a1 + a3)));
                        a[i + offset + 2 * p] = mint::from(a0 + na2 + a1na3imag);
                        a[i + offset + 3 * p] = mint::from(a0 + na2 + (mod2 - a1na3imag));
                    }
                    if s + 1 != (1 << len) {
                        rot *= info.rate3[bsf(!s)];
                    }
                }
                len += 2;
            }
        }
    }
    fn butterfly_inv(a: &mut [mint]) {
        let n = a.len();
        let h = ceil_pow2(n);

        let info = FFTinfo::new();

        let mut len = h; // a[i, i+(n>>len), i+2*(n>>len), ..] is transformed
        while len > 0 {
            if len == 1 {
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                for s in 0..(1 << (len - 1)) {
                    let offset = s << (h - len + 1);
                    for i in 0..p {
                        let l = a[i + offset];
                        let r = a[i + offset + p];
                        a[i + offset] = l + r;
                        a[i + offset + p] =
                            mint::from((mint::get_mod() + l.val() - r.val()) * irot.val());
                    }
                    if s + 1 != (1 << (len - 1)) {
                        irot *= info.irate2[bsf(!s)];
                    }
                }
                len -= 1;
            } else {
                // 4-base
                let p = 1 << (h - len);
                let mut irot = mint::from(1);
                let iimag = info.iroot[2];
                for s in 0..(1 << (len - 2)) {
                    let irot2 = irot * irot;
                    let irot3 = irot2 * irot;
                    let offset = s << (h - len + 2);
                    for i in 0..p {
                        let a0 = a[i + offset].val();
                        let a1 = a[i + offset + p].val();
                        let a2 = a[i + offset + 2 * p].val();
                        let a3 = a[i + offset + 3 * p].val();
                        let a2na3iimag =
                            mint::from((mint::get_mod() + a2 - a3) * iimag.val()).val();
                        a[i + offset] = mint::from(a0 + a1 + a2 + a3);
                        a[i + offset + p] =
                            mint::from((a0 + (mint::get_mod() - a1) + a2na3iimag) * irot.val());
                        a[i + offset + 2 * p] = mint::from(
                            (a0 + a1 + (mint::get_mod() - a2) + (mint::get_mod() - a3))
                                * irot2.val(),
                        );
                        a[i + offset + 3 * p] = mint::from(
                            (a0 + (mint::get_mod() - a1) + (mint::get_mod() - a2na3iimag))
                                * irot3.val(),
                        );
                    }
                    if s + 1 != (1 << (len - 2)) {
                        irot *= info.irate3[bsf(!s)];
                    }
                }
                len -= 2;
            }
        }
    }
}
use convolution::convolution;

mod manhattan_mst {
    use crate::change_min_max::ChangeMinMax;
    use crate::{segment_tree::SegmentTree, CoordinateCompress, UnionFind};
    use std::cmp::{min, Reverse};
    use std::collections::BinaryHeap;
    pub struct ManhattanMST {
        points: Vec<(usize, (i64, i64))>,
    }
    impl ManhattanMST {
        pub fn new() -> Self {
            Self { points: vec![] }
        }
        pub fn push(&mut self, pt: (i64, i64)) {
            self.points.push((self.points.len(), pt));
        }
        fn mst(mut edges: Vec<(i64, usize, usize)>, n: usize) -> Vec<Vec<(i64, usize)>> {
            let mut uf = UnionFind::new(n);
            let mut g = vec![vec![]; n];
            edges.sort();
            for (delta, i, j) in edges {
                if !uf.same(i, j) {
                    uf.unite(i, j);
                    g[i].push((delta, j));
                    g[j].push((delta, i));
                }
            }
            g
        }
        pub fn minimum_spanning_tree(&mut self) -> Vec<Vec<(i64, usize)>> {
            let n = self.points.len();
            let mut edges = vec![];
            let inf = 1i64 << 60;
            for h0 in 0..2 {
                for h1 in 0..2 {
                    let y_enc = self
                        .points
                        .iter()
                        .map(|&(_i, (y, _x))| y)
                        .collect::<Vec<_>>()
                        .compress_encoder();
                    for h2 in 0..2 {
                        let mut st = SegmentTree::<(usize, i64)>::new(
                            n,
                            |(i0, ypx0), (i1, ypx1)| {
                                if ypx0 < ypx1 {
                                    (i0, ypx0)
                                } else {
                                    (i1, ypx1)
                                }
                            },
                            (0, inf),
                        );
                        self.points
                            .sort_by(|(_i0, (y0, x0)), (_i1, (y1, x1))| (y0 - x0).cmp(&(y1 - x1)));
                        for &(i, (y, x)) in self.points.iter() {
                            let ey = y_enc[&y];
                            let q = st.query(ey, n - 1);
                            if q.1 != inf {
                                let delta = q.1 - (y + x);
                                debug_assert!(delta >= 0);
                                edges.push((delta, i, q.0));
                            }
                            //
                            if st.get(ey).1 > y + x {
                                st.set(ey, (i, y + x));
                            }
                        }
                        if h2 == 0 {
                            self.points.iter_mut().for_each(|(_i, (_y, x))| *x = -(*x));
                        }
                    }
                    if h1 == 0 {
                        self.points.iter_mut().for_each(|(_i, (y, _x))| *y = -(*y));
                    }
                }
                if h0 == 0 {
                    self.points
                        .iter_mut()
                        .for_each(|(_i, (y, x))| std::mem::swap(x, y));
                }
            }
            Self::mst(edges, n)
        }
    }
}
use manhattan_mst::ManhattanMST;

mod mo {
    use std::iter::{Chain, Rev};
    use std::ops::{Range, RangeInclusive};
    use std::vec::IntoIter;
    pub struct Mo {
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    pub struct MoIterator {
        index_iter: IntoIter<usize>,
        ls: Vec<usize>,
        rs: Vec<usize>,
    }
    impl Mo {
        pub fn new() -> Self {
            Self {
                ls: vec![],
                rs: vec![],
            }
        }
        pub fn add_range_queue(&mut self, l: usize, r: usize) {
            self.ls.push(l);
            self.rs.push(r);
        }
        pub fn into_iter(self) -> MoIterator {
            let n = self.rs.iter().max().unwrap() + 1;
            let q = self.rs.len();
            let d = n / ((q as f64).sqrt() as usize + 1) + 1;
            let mut indexes = (0..q).collect::<Vec<_>>();
            indexes.sort_by_cached_key(|&i| {
                let div = self.ls[i] / d;
                if div % 2 == 0 {
                    (div, self.rs[i])
                } else {
                    (div, n - self.rs[i])
                }
            });
            MoIterator {
                index_iter: indexes.into_iter(),
                ls: self.ls,
                rs: self.rs,
            }
        }
        pub fn add_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Rev<Range<usize>>, RangeInclusive<usize>> {
            (l1..l0).rev().chain(r0 + 1..=r1)
        }
        pub fn remove_chain(
            l0: usize,
            r0: usize,
            l1: usize,
            r1: usize,
        ) -> Chain<Range<usize>, Rev<RangeInclusive<usize>>> {
            (l0..l1).chain(((r1 + 1)..=r0).rev())
        }
    }
    impl Iterator for MoIterator {
        type Item = (usize, (usize, usize));
        fn next(&mut self) -> Option<Self::Item> {
            if let Some(i) = self.index_iter.next() {
                Some((i, (self.ls[i], self.rs[i])))
            } else {
                None
            }
        }
    }
}
use mo::*;

mod heavy_light_decomposition {
    use crate::ChangeMinMax;
    use crate::UnionFind;

    // use entry order as inclusive array range, for segment-tree.
    pub struct Hld {
        entry_order: Vec<usize>, // order of entrying each node
        leave_order: Vec<usize>, // order of leaving each node
        head_of: Vec<usize>,     // the shallowest node of heavy path that the node belongs to.
        sub_size: Vec<usize>,    // subtree size.
        g: Vec<Vec<usize>>,      // linked-list graph.
        root: usize,             // root of whole tree
        uf: UnionFind,           // for a trigger of auto build
        par: Vec<usize>,         // parent for each node
        depth: Vec<usize>,       // step distance from root
    }
    impl Hld {
        pub fn new(n: usize, root: usize) -> Self {
            Self {
                entry_order: vec![n; n],
                leave_order: vec![n; n],
                head_of: vec![n; n],
                sub_size: vec![n + 1; n],
                g: vec![vec![]; n],
                root,
                uf: UnionFind::new(n),
                par: vec![n; n],
                depth: vec![n; n],
            }
        }
        pub fn add_edge(&mut self, a: usize, b: usize) {
            self.g[a].push(b);
            self.g[b].push(a);
            self.uf.unite(a, b);
            if self.uf.group_num() == 1 {
                self.build();
            }
        }
        fn build(&mut self) {
            self.depth[self.root] = 0;
            self.dfs_sz(self.root, self.g.len());
            self.dfs_hld(self.root, self.g.len(), self.root, &mut 0);
        }
        fn dfs_sz(&mut self, v: usize, pre: usize) {
            self.sub_size[v] = 1;
            for nv in self.g[v].clone() {
                if nv == pre {
                    continue;
                }
                self.par[nv] = v;
                self.depth[nv] = self.depth[v] + 1;
                self.dfs_sz(nv, v);
                self.sub_size[v] += self.sub_size[nv];
            }
        }
        fn dfs_hld(&mut self, v: usize, pre: usize, head: usize, vis_cnt: &mut usize) {
            self.head_of[v] = head;
            self.entry_order[v] = *vis_cnt;
            *vis_cnt += 1;
            let mut sub_size_max = None;
            let mut sub_size_max_ei = 0;
            for (ei, nv) in self.g[v].iter().copied().enumerate() {
                if nv == pre {
                    continue;
                }
                if sub_size_max.chmax(self.sub_size[nv]) {
                    sub_size_max_ei = ei;
                }
            }
            if sub_size_max.is_some() {
                // set heavy child at g[v][0]
                if sub_size_max_ei != 0 {
                    self.g[v].swap(0, sub_size_max_ei);
                }

                for (ei, nv) in self.g[v].clone().into_iter().enumerate() {
                    if nv == pre {
                        continue;
                    }
                    let nhead = if ei == 0 { head } else { nv };
                    self.dfs_hld(nv, v, nhead, vis_cnt);
                }
            }
            self.leave_order[v] = *vis_cnt;
        }
        pub fn lca(&self, mut a: usize, mut b: usize) -> usize {
            while self.head_of[a] != self.head_of[b] {
                if self.entry_order[self.head_of[a]] > self.entry_order[self.head_of[b]] {
                    a = self.par[self.head_of[a]];
                } else {
                    b = self.par[self.head_of[b]];
                }
            }
            if self.depth[a] < self.depth[b] {
                a
            } else {
                b
            }
        }
        pub fn edges_to_arrayranges(&self, mut a: usize, mut b: usize) -> Vec<(usize, usize)> {
            let mut ret = vec![];
            while self.head_of[a] != self.head_of[b] {
                if self.entry_order[self.head_of[a]] > self.entry_order[self.head_of[b]] {
                    ret.push((self.entry_order[self.head_of[a]], self.entry_order[a]));
                    a = self.par[self.head_of[a]];
                } else {
                    ret.push((self.entry_order[self.head_of[b]], self.entry_order[b]));
                    b = self.par[self.head_of[b]];
                }
            }
            match self.depth[a].cmp(&self.depth[b]) {
                std::cmp::Ordering::Less => {
                    ret.push((self.entry_order[self.g[a][0]], self.entry_order[b]));
                }
                std::cmp::Ordering::Greater => {
                    ret.push((self.entry_order[self.g[b][0]], self.entry_order[a]));
                }
                _ => {}
            }
            ret
        }
        pub fn nodes_to_arrayranges(&self, a: usize, b: usize) -> Vec<(usize, usize)> {
            let mut ret = self.edges_to_arrayranges(a, b);
            let l = self.lca(a, b);
            ret.push((self.entry_order[l], self.entry_order[l]));
            ret
        }
        pub fn subnodes_to_arrayrange(&self, subroot: usize) -> (usize, usize) {
            (self.entry_order[subroot], self.leave_order[subroot])
        }
    }
}
use heavy_light_decomposition::Hld;

// construct XOR basis.
// Some XOR combination of these can make every element of the array.
// When msb of a[i] is b-th, b-th bit of all the other element is zero.
fn xor_basis(a: &[usize]) -> Vec<usize> {
    let mut basis: Vec<usize> = vec![];
    for mut a in a.iter().copied() {
        for &base in basis.iter() {
            a.chmin(a ^ base);
        }
        for base in basis.iter_mut() {
            base.chmin(a ^ *base);
        }
        if a > 0 {
            basis.push(a);
        }
    }
    basis.sort();
    basis
}

mod procon_reader {
    use std::fmt::Debug;
    use std::io::Read;
    use std::str::FromStr;
    pub fn read<T: FromStr>() -> T
    where
        <T as FromStr>::Err: Debug,
    {
        let stdin = std::io::stdin();
        let mut stdin_lock = stdin.lock();
        let mut u8b: [u8; 1] = [0];
        loop {
            let mut buf: Vec<u8> = Vec::with_capacity(16);
            loop {
                let res = stdin_lock.read(&mut u8b);
                if res.unwrap_or(0) == 0 || u8b[0] <= b' ' {
                    break;
                } else {
                    buf.push(u8b[0]);
                }
            }
            if !buf.is_empty() {
                let ret = String::from_utf8(buf).unwrap();
                return ret.parse().unwrap();
            }
        }
    }
    pub fn read_vec<T: std::str::FromStr>(n: usize) -> Vec<T>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..n).map(|_| read::<T>()).collect::<Vec<T>>()
    }
    pub fn read_vec_sub1(n: usize) -> Vec<usize> {
        (0..n).map(|_| read::<usize>() - 1).collect::<Vec<usize>>()
    }
    pub fn read_mat<T: std::str::FromStr>(h: usize, w: usize) -> Vec<Vec<T>>
    where
        <T as FromStr>::Err: Debug,
    {
        (0..h).map(|_| read_vec::<T>(w)).collect::<Vec<Vec<T>>>()
    }
}
use procon_reader::*;
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

use std::time::Instant;
use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaChaRng;
const TEMP_MAX: usize = 1000;
const SET_SIG_RATE: f64 = 1.0;
const D: usize = 2;
const TIME_LIMIT:u128 = 3_000;
struct Solver {
    t0: Instant,
    l: usize,
    n: usize,
    s: f64,
    gates: Vec<(usize, usize)>,
    rand: XorShift64,
    rng: ChaChaRng,
    base: usize,
    deltas: BTreeSet<(usize, usize)>,
    value_order: Vec<usize>,
}
impl Solver {
    fn new() -> Self {
        let t0 = Instant::now();
        let l = read::<usize>();
        let n = read::<usize>();
        let s = read::<f64>();
        let gates = (0..n).map(|_| (read::<usize>(), read::<usize>())).collect::<Vec<_>>();
        let rand = XorShift64::new();
        let seed = [0; 32];
        let rng = ChaChaRng::from_seed(seed);

        let div_unit = (2.0 * SET_SIG_RATE * s) as usize;
        let base = max(2, TEMP_MAX / div_unit);
        let mut width = 1usize;
        while base.pow(width as u32) < n {
            width += 1;
        }
        eprintln!("base: {}, width: {}", base, width);
        let p = D % l;
        let m = (l - D) % l;
        let mut deltas = BTreeSet::new();
        for &delta in vec![
            (0, 0),
            (p, 0),
            (0, p),
            (m, 0),
            (0, m),
            (p, p),
            (p, m),
            (m, p),
            (m, m),
        ].iter().take(width) {
            deltas.insert(delta);
        }
        let value_order = (0..base.pow(width as u32)).collect::<Vec<_>>();
        Self { t0, l, n, s, gates, rand, rng, base, deltas, value_order }
    }
    fn gen_vals(&mut self) -> Option<Vec<usize>> {
        let mut val_remains = vec![true; self.base.pow(self.deltas.len() as u32)];
        let mut field = vec![vec![None; self.l]; self.l];
        let mut values = vec![0; self.n];
        for (gi, (y0, x0)) in self.gates.iter().copied().enumerate() {
            let mut valset = false;
            for gate_val0 in (0..val_remains.len()).map(|i| self.value_order[i]).filter(|&value| val_remains[value]) {
                let mut digit_ok = true;
                let mut gate_val = gate_val0;
                for (dy, dx) in self.deltas.iter().copied().take(self.deltas.len()) {
                    let y = (y0 + dy) % self.l;
                    let x = (x0 + dx) % self.l;
                    let digit = gate_val % self.base;
                    gate_val /= self.base;
                    if let Some(org) = field[y][x] {
                        if org != digit {
                            digit_ok = false;
                            break;
                        }
                    }
                }
                if !digit_ok {
                    continue;
                }
                // found valid value!
                let mut gate_val = gate_val0;
                for (dy, dx) in self.deltas.iter().copied() {
                    let y = (y0 + dy) % self.l;
                    let x = (x0 + dx) % self.l;
                    let digit = gate_val % self.base;
                    gate_val /= self.base;
                    if field[y][x].is_some() {
                        debug_assert!(field[y][x].unwrap() == digit);
                        continue;
                    }
                    field[y][x] = Some(digit);
                }
                val_remains[gate_val0] = false;
                values[gi] = gate_val0;
                valset = true;
                break;
            }

            if !valset {
                return None;
            }
        }
        if cfg!(debug_assertions) {
            let mut st = BTreeSet::new();
            for v in values.iter().copied() {
                st.insert(v);
                debug_assert!(v < self.base.pow(self.deltas.len() as u32));
            }
            debug_assert!(st.len() == values.len());
            let mut field = vec![vec![None; self.l]; self.l];
            for (gi, gvalue) in values.iter().copied().enumerate() {
                let (gy, gx) = self.gates[gi];
                for (di, (dy, dx)) in self.deltas.iter().copied().enumerate() {
                    let y = (gy + dy) % self.l;
                    let x = (gx + dx) % self.l;
                    let mut digit = gvalue;
                    for _ in 0..di {
                        digit /= self.base;
                    }
                    digit %= self.base;
                    if let Some(org) = field[y][x] {
                        debug_assert!(org == digit);
                    } else {
                        field[y][x] = Some(digit);
                    }
                }
            }
        }
        Some(values)
    }
    fn gen_vals_ini(&mut self) -> Vec<usize> {
        let lmax = self.base.pow(self.deltas.len() as u32);
        let mut ret = vec![];
        for _ in 0..self.n {
            let l = self.rand.next_usize() % lmax;
            ret.push(l);
        }
        ret
    }
    fn calc_set_temp(&self, level: usize) -> usize {
        debug_assert!(level < self.base);
        let unit = TEMP_MAX as f64 / (self.base - 1) as f64;
        min((unit * level as f64) as usize, TEMP_MAX)
    }
    fn gen_temp_map(&self, values: &[usize]) -> Vec<Vec<usize>> {
        let mut temp = vec![vec![0; self.l]; self.l];
        let mut done = vec![vec![false; self.l]; self.l];
        let mut temp_sum = 0;
        let mut temp_norm = 0;
        for ((y0, x0), val0) in self.gates.iter().zip(values.iter().copied()) {
            let mut val = val0;
            for (dy, dx) in self.deltas.iter().copied() {
                let y = (y0 + dy) % self.l;
                let x = (x0 + dx) % self.l;
                let level = val % self.base;
                val /= self.base;
                let temp_val = self.calc_set_temp(level);
                if done[y][x] {
                    debug_assert!(temp[y][x] == temp_val);
                    continue;
                }
                temp[y][x] = temp_val;
                done[y][x] = true;
                temp_sum += temp_val;
                temp_norm += 1;
            }
        }
        let temp_mean = temp_sum / temp_norm;
        for y in 0..self.l {
            for x in 0..self.l {
                if done[y][x] {
                    continue;
                }
                temp[y][x] = temp_mean;
            }
        }
        // smoothing
        let rate = 0.1;
        for _ in 0..20 {
            let mut grad = vec![vec![0; self.l]; self.l];
            let mut grad_abs_sum = 0;
            for y0 in 0..self.l {
                for x0 in 0..self.l {
                    for &(dy, dx) in [(0, 1), (1, 0)].iter() {
                        let y1 = (y0 + dy) % self.l;
                        let x1 = (x0 + dx) % self.l;
                        let rise_grad0 = 2 * (temp[y0][x0] as i64 - temp[y1][x1] as i64);
                        let rise_grad1 = - rise_grad0;
                        if !done[y0][x0] {
                            grad[y0][x0] += rise_grad0;
                            grad_abs_sum += rise_grad0.abs();
                        }
                        if !done[y1][x1] {
                            grad[y1][x1] += rise_grad1;
                            grad_abs_sum += rise_grad1.abs();
                        }
                    }
                }
            }
            if grad_abs_sum == 0 {
                break;
            }
            for y in 0..self.l {
                for x in 0..self.l {
                    if done[y][x] {
                        continue;
                    }
                    let t = (temp[y][x] as f64 - rate * grad[y][x] as f64) as i64;
                    temp[y][x] = max(0, min(TEMP_MAX as i64, t)) as usize;
                }
            }
        }
        temp
    }
    fn calc_temp_cost(&self, temp: &[Vec<usize>]) -> i64 {
        let mut cost = 0;
        for y in 0..self.l {
            for x in 0..self.l {
                for &(dy, dx) in [(0, 1), (1, 0)].iter() {
                    let ny = (y + dy) % self.l;
                    let nx = (x + dx) % self.l;
                    let dt = temp[ny][nx] as i64 - temp[y][x] as i64;
                    cost += dt * dt;
                }
            }
        }
        cost
    }
    fn output_temp(temp: &[Vec<usize>]) {
        for temp_row in temp.iter() {
            for temp_val in temp_row.iter() {
                print!("{} ", temp_val);
            }
            println!();
        }
    }
    fn ask(i: usize, dy: usize, dx: usize) -> usize {
        println!("{} {} {}", i, dy, dx);
        read::<usize>()
    }
    fn measure(&self, set_values: &[usize]) -> Vec<usize> {
        let mut sum = vec![vec![0usize; self.deltas.len()]; self.n];
        let mut norm = vec![vec![0usize; self.deltas.len()]; self.n];
        let mut ask_cnt = 0usize;
        let mut tgt_st = BTreeSet::new();
        for val in set_values.iter().copied() {
            tgt_st.insert(val);
        }
        debug_assert!(set_values.len() == tgt_st.len());
        let mut get_value = vec![0; self.n];
        loop {
            'scan: for gi in 0..self.n {
                for (di, (dy, dx)) in self.deltas.iter().copied().enumerate() {
                    let m = Self::ask(gi, dy, dx);
                    sum[gi][di] += m;
                    norm[gi][di] += 1;
                    ask_cnt += 1;
                    if ask_cnt >= 10000 {
                        break 'scan;
                    }
                }
            }

            get_value.iter_mut().for_each(|v| *v = 0);
            for gi in 0..self.n {
                for di in 0..self.deltas.len() {
                    debug_assert!(norm[gi][di] > 0);
                    let meas_mean = sum[gi][di] as f64 / norm[gi][di] as f64;
                    let mut delta_max = None;
                    let mut level = 0;
                    for li in 0..self.base {
                        let infer_value = self.calc_set_temp(li) as f64;
                        let infer_delta = (infer_value - meas_mean).abs();
                        if delta_max.chmin(infer_delta) {
                            level = li;
                        }
                    }
                    get_value[gi] += self.base.pow(di as u32) * level;
                }
            }

            let mut get_st = BTreeSet::new();
            for val in get_value.iter().copied() {
                get_st.insert(val);
            }
            if get_st == tgt_st {
                eprintln!("FULL MATCH!");
                break;
            }
            if ask_cnt >= 10000 {
                break;
            }
        }
        get_value
    }
    fn answer(&self, set_values: Vec<usize>, get_values: Vec<usize>) {
        let mut set_remains = BTreeSet::new();
        for i in 0..self.n {
            set_remains.insert(i);
        }
        let mut ans = vec![None; self.n];
        for (gi, gv) in get_values.iter().copied().enumerate() {
            for (si, sv) in set_values.iter().copied().enumerate() {
                if gv != sv {
                    continue;
                }
                if !set_remains.contains(&si) {
                    continue;
                }
                ans[gi] = Some(si);
                set_remains.remove(&si);
                break;
            }
        }
        for (gi, ans) in ans.iter_mut().enumerate() {
            if ans.is_some() {
                continue;
            }
            let mut dmin = None;
            let mut nxt = 0;
            for si in set_remains.iter().copied() {
                let d = (set_values[si] ^ get_values[gi]).count_ones();
                if dmin.chmin(d) {
                    nxt = si;
                }
            }
            set_remains.remove(&nxt);
            *ans = Some(nxt);
        }
        println!("-1 -1 -1");
        for ans in ans.into_iter().flatten() {
            println!("{}", ans);
        }
    }
    fn solve(&mut self) {
        let mut best_values = self.gen_vals_ini();
        // gen temperature map
        let mut best_temp = self.gen_temp_map(&best_values);
        let mut best_temp_cost = self.calc_temp_cost(&best_temp);
        let mut try_cnt = 0usize;
        let mut update_cnt = 0usize;
        let mut invalid_cnt = 0usize;
        let mut trans = false;
        while self.t0.elapsed().as_millis() < TIME_LIMIT {
            try_cnt += 1;
            let vl = self.value_order.len();
            let i0 = self.rand.next_usize() % vl;
            let i1 = (i0 + 1 + self.rand.next_usize() % (vl - 1)) % vl;
            assert!(i0 != i1);
            if !trans {
                self.value_order.shuffle(&mut self.rng);
            } else {
                self.value_order.swap(i0, i1);
            }
            if let Some(values) = self.gen_vals() {
                let temp = self.gen_temp_map(&values);
                let temp_cost = self.calc_temp_cost(&temp);
                if best_temp_cost.chmin(temp_cost) {
                    update_cnt += 1;
                    best_values = values;
                    best_temp = temp;
                    trans = true;
                } else {
                    if trans {
                        self.value_order.swap(i0, i1);
                    }
                }
            } else {
                if trans {
                    self.value_order.swap(i0, i1);
                }
                invalid_cnt += 1;
            }
            if update_cnt == 0 && self.t0.elapsed().as_millis() > 1000 && invalid_cnt >= 1000 {
                let mut add_cnt = 0;
                invalid_cnt = 0;
                for d in D.. {
                    let mut cands = vec![];
                    for dy in - (self.l as i64 - 1)..self.l as i64 {
                        for dx in - (self.l as i64 - 1)..self.l as i64 {
                            let dyx = (dy.abs() + dx.abs()) as usize;
                            if dyx != d {
                                continue;
                            }
                            let dy = ((dy + self.l as i64) % self.l as i64) as usize;
                            let dx = ((dx + self.l as i64) % self.l as i64) as usize;
                            if !self.deltas.contains(&(dy, dx)) {
                                cands.push((dy, dx));
                            }
                        }
                    }
                    if cands.is_empty() {
                        continue;
                    }
                    let mut corder = (0..cands.len()).collect::<Vec<_>>();
                    corder.shuffle(&mut self.rng);
                    for co in corder {
                        self.deltas.insert(cands[co]);
                        add_cnt += 1;
                        if add_cnt >= 4 {
                            break;
                        }
                    }
                    if add_cnt >= 4 {
                        break;
                    }
                }
                while self.value_order.len() < self.base.pow(self.deltas.len() as u32) {
                    self.value_order.push(self.value_order.len());
                }
            }
        }
        eprintln!("{}/{}", update_cnt, try_cnt);
        Self::output_temp(&best_temp);
        // question until adjascent temp delta is smaller than sigma
        let get_values = self.measure(&best_values);
        self.answer(best_values, get_values);
    }
}
fn main() {
    let mut solver = Solver::new();
    solver.solve();
}