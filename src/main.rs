#![allow(unused_macros, unused_imports, dead_code)]
use num::{One, Zero};
use permutohedron::LexicalPermutation;
use rand::{seq::SliceRandom, SeedableRng};
use rand_chacha::ChaChaRng;
use std::any::TypeId;
use std::cmp::{max, min, Ordering, Reverse};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, HashMap, HashSet, VecDeque};
use std::mem::swap;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, Sub, SubAssign};
use std::time::Instant;
//let mut rng = ChaChaRng::from_seed([0; 32]);

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
    use num::{One, Zero};
    use std::cmp::{PartialEq, PartialOrd};
    use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign};
    pub fn gcd<T: Copy + Rem<Output = T> + PartialEq + Zero>(a: T, b: T) -> T {
        if b == T::zero() {
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
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + Zero
            + One,
    >(
        a: T,
        b: T,
    ) -> (T, T) {
        if a == T::zero() {
            return (T::zero(), T::one());
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
            + RemAssign
            + Zero
            + One,
    >(
        m1: T,
        r1: T,
        m2: T,
        r2: T,
    ) -> Option<(T, T)> {
        let (p, _q) = ext_gcd(m1, m2);
        let g = gcd(m1, m2);
        if (r2 - r1) % g != T::zero() {
            None
        } else {
            let lcm = m1 * (m2 / g);
            let mut r = r1 + m1 * ((r2 - r1) / g) * p;
            if r < T::zero() {
                let dv = (-r + lcm - T::one()) / lcm;
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
            + RemAssign
            + One
            + Zero,
    >(
        mods: &[T],
        rems: &[T],
    ) -> Option<(T, T)> {
        debug_assert!(mods.len() == rems.len());
        let mut lcm = T::one();
        let mut rem = T::zero();
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
    T: Clone
        + Copy
        + From<usize>
        + Into<usize>
        + Mul<Output = T>
        + Div<Output = T>
        + One
        + Zero
        + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if n < k {
        return T::zero();
    }
    if k == 0 {
        return T::one();
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return (T::from(n) * T::from(n - 1)) / T::from(2);
    }

    factorial::<T>(n) * factorial_inv::<T>(k) * factorial_inv::<T>(n - k)
}

fn permutation<
    T: Clone + Copy + From<usize> + Into<usize> + Mul<Output = T> + Div<Output = T> + One + 'static,
>(
    n: usize,
    k: usize,
) -> T {
    if k == 0 {
        return T::one();
    } else if k == 1 {
        return T::from(n);
    } else if k == 2 {
        return T::from(n) * T::from(n - 1);
    }

    factorial::<T>(n) * factorial_inv::<T>(n - k)
}

mod union_find {
    #[derive(Debug, Clone)]
    pub struct UnionFind {
        pub graph: Vec<Vec<usize>>,
        potential: Vec<i64>,
        parents: Vec<usize>,
        grp_sz: Vec<usize>,
        grp_num: usize,
    }

    impl UnionFind {
        pub fn new(sz: usize) -> Self {
            Self {
                graph: vec![vec![]; sz],
                potential: vec![0; sz],
                parents: (0..sz).collect::<Vec<usize>>(),
                grp_sz: vec![1; sz],
                grp_num: sz,
            }
        }
        pub fn root(&mut self, v: usize) -> usize {
            if v == self.parents[v] {
                v
            } else {
                let pv = self.parents[v];
                let rv = self.root(pv);
                self.potential[v] += self.potential[pv];
                self.parents[v] = rv;
                self.parents[v]
            }
        }
        pub fn get_delta(&mut self, v0: usize, v1: usize) -> Option<i64> {
            if !self.same(v0, v1) {
                return None;
            }
            Some(self.potential[v1] - self.potential[v0])
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.root(a) == self.root(b)
        }
        pub fn unite(&mut self, into: usize, from: usize) {
            self.unite_with_delta(into, from, 0);
        }
        pub fn unite_with_delta(&mut self, into: usize, from: usize, delta: i64) {
            self.graph[into].push(from);
            self.graph[from].push(into);
            let r_into = self.root(into);
            let r_from = self.root(from);
            if r_into != r_from {
                self.parents[r_from] = r_into;
                self.potential[r_from] = self.potential[into] - self.potential[from] + delta;
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
        n: usize,
        dat: Vec<T>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Clone> SegmentTree<T> {
        pub fn new(n: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            let mut s = Self {
                n,
                pair_op,
                dat: vec![ini_val.clone(); 2 * n],
            };
            for i in 0..n {
                s.set(i, ini_val.clone());
            }
            s
        }
        pub fn from_vec(pair_op: fn(T, T) -> T, ini_values: Vec<T>) -> Self {
            let n = ini_values.len();
            let mut st = Self {
                n,
                pair_op,
                dat: vec![ini_values[0].clone(); 2 * n],
            };
            for (i, ini_val) in ini_values.iter().enumerate() {
                st.set(i, ini_val.clone());
            }
            st
        }
        pub fn set(&mut self, mut pos: usize, val: T) {
            pos += self.n;
            self.dat[pos] = val;
            let mut par = pos / 2;
            while par >= 1 {
                let l = par * 2;
                let r = l + 1;
                self.dat[par] = (self.pair_op)(self.dat[l].clone(), self.dat[r].clone());
                par /= 2;
            }
        }
        pub fn get(&self, pos: usize) -> T {
            self.dat[pos + self.n].clone()
        }
        // get query value of [a, b]
        pub fn query(&self, mut a: usize, mut b: usize) -> T {
            a += self.n;
            b += self.n + 1;
            let mut aval = None;
            let mut bval = None;
            while a < b {
                if a % 2 == 1 {
                    aval = if let Some(aval0) = aval {
                        Some((self.pair_op)(aval0, self.dat[a].clone()))
                    } else {
                        Some(self.dat[a].clone())
                    };
                    a += 1;
                }
                if b % 2 == 1 {
                    b -= 1;
                    bval = if let Some(bval0) = bval {
                        Some((self.pair_op)(self.dat[b].clone(), bval0))
                    } else {
                        Some(self.dat[b].clone())
                    };
                }
                a /= 2;
                b /= 2;
            }
            if let Some(aval) = aval {
                if let Some(bval) = bval {
                    (self.pair_op)(aval, bval)
                } else {
                    aval
                }
            } else {
                bval.unwrap()
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
mod segment_tree_2d {
    use std::ops::{Add, Sub};

    use crate::segment_tree::SegmentTree;
    #[derive(Debug, Clone)]
    pub struct SegmentTree2D<T> {
        h: usize,
        w: usize,
        segs: Vec<SegmentTree<T>>,
        pair_op: fn(T, T) -> T,
    }
    impl<T: Clone> SegmentTree2D<T> {
        pub fn new(h: usize, w: usize, pair_op: fn(T, T) -> T, ini_val: T) -> Self {
            Self {
                h,
                w,
                pair_op,
                segs: vec![SegmentTree::new(w, pair_op, ini_val); 2 * h],
            }
        }
        pub fn set(&mut self, mut y: usize, x: usize, val: T) {
            y += self.h;
            self.segs[y].set(x, val);
            let mut par = y / 2;
            while par >= 1 {
                let l = par * 2;
                let r = l + 1;
                let lv = self.segs[l].get(x);
                let rv = self.segs[r].get(x);
                let v = (self.pair_op)(lv, rv);
                self.segs[par].set(x, v);
                par /= 2;
            }
        }
        pub fn get(&self, y: usize, x: usize) -> T {
            self.segs[y + self.h].get(x)
        }
        // get query value of [a, b]
        pub fn query(&self, mut y0: usize, mut y1: usize, x0: usize, x1: usize) -> T {
            y0 += self.h;
            y1 += self.h + 1;
            let mut y0val = None;
            let mut bval = None;
            while y0 < y1 {
                if y0 % 2 == 1 {
                    y0val = if let Some(aval0) = y0val {
                        Some((self.pair_op)(aval0, self.segs[y0].query(x0, x1)))
                    } else {
                        Some(self.segs[y0].query(x0, x1))
                    };
                    y0 += 1;
                }
                if y1 % 2 == 1 {
                    y1 -= 1;
                    bval = if let Some(bval0) = bval {
                        Some((self.pair_op)(self.segs[y1].query(x0, x1), bval0))
                    } else {
                        Some(self.segs[y1].query(x0, x1))
                    };
                }
                y0 /= 2;
                y1 /= 2;
            }
            if let Some(y0val) = y0val {
                if let Some(bval) = bval {
                    (self.pair_op)(y0val, bval)
                } else {
                    y0val
                }
            } else {
                bval.unwrap()
            }
        }
    }
    impl<T: Copy + Add<Output = T> + Sub<Output = T>> SegmentTree2D<T> {
        pub fn add(&mut self, y: usize, x: usize, add_val: T) {
            self.set(y, x, self.get(y, x) + add_val);
        }
        pub fn sub(&mut self, y: usize, x: usize, sub_val: T) {
            self.set(y, x, self.get(y, x) - sub_val);
        }
    }
    mod tests {
        #[test]
        fn random_test() {
            use super::super::XorShift64;
            use super::SegmentTree2D;
            use std::cmp::{max, min};
            const N: usize = 10;
            let mut rand = XorShift64::new();
            for &f in [min, max, |x, y| x + y].iter() {
                let mut raw = vec![vec![0; N]; N];
                let mut seg = SegmentTree2D::<i64>::new(N, N, f, 0);
                for y in 0..N {
                    for x in 0..N {
                        let v = rand.next_u64() as i64 % 100;
                        seg.set(y, x, v);
                        raw[y][x] = v;
                    }
                }
                for y0 in 0..N {
                    for y1 in y0..N {
                        for x0 in 0..N {
                            for x1 in x0..N {
                                let seg_v = seg.query(y0, y1, x0, x1);
                                let mut raw_v = raw[y0][x0];
                                for y in y0..=y1 {
                                    for x in x0..=x1 {
                                        if (y, x) == (y0, x0) {
                                            continue;
                                        }
                                        raw_v = f(raw_v, raw[y][x]);
                                    }
                                }
                                assert_eq!(seg_v, raw_v);
                            }
                        }
                    }
                }
            }
        }
    }
}
use segment_tree_2d::SegmentTree2D;

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
    use num::{One, Zero};
    use std::fmt;
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, Sub, SubAssign};

    #[derive(Clone, Copy, Eq, Hash, PartialEq)]
    pub struct ModInt<const MOD: i64> {
        x: i64,
    }
    impl<const MOD: i64> ModInt<MOD> {
        pub fn val(&self) -> i64 {
            self.x
        }
        fn new(mut sig: i64) -> Self {
            if sig < 0 {
                let ab = (-sig + MOD - 1) / MOD;
                sig += ab * MOD;
                debug_assert!(sig >= 0);
            }
            Self { x: sig % MOD }
        }
        fn inverse(&self) -> Self {
            // x * inv_x + M * _ = 1 (mod M)
            Self::new(ext_gcd(self.x, MOD).0)

            // [Fermat's little theorem]
            // if p is prime, for any integer a, a^p = a (mod p)
            // especially when a and b is coprime, a^(p-1) = 1 (mod p).
            // -> inverse of a is a^(p-2).

            //let mut ret = Self { x: 1 };
            //let mut mul: Self = *self;
            //let mut p = MOD() - 2;
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
            let mut ret = Self::one();
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
    impl<const MOD: i64> One for ModInt<MOD> {
        fn one() -> Self {
            Self { x: 1 }
        }
    }
    impl<const MOD: i64> Zero for ModInt<MOD> {
        fn zero() -> Self {
            Self { x: 0 }
        }
        fn is_zero(&self) -> bool {
            self.x == 0
        }
        fn set_zero(&mut self) {
            self.x = 0;
        }
    }
    impl<const MOD: i64> AddAssign<Self> for ModInt<MOD> {
        fn add_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x + rhs.x);
        }
    }
    impl<const MOD: i64> Add<ModInt<MOD>> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn add(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x + rhs.x)
        }
    }
    impl<const MOD: i64> Add<i64> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn add(self, rhs: i64) -> Self::Output {
            self + ModInt::new(rhs)
        }
    }
    impl<const MOD: i64> Add<ModInt<MOD>> for i64 {
        type Output = ModInt<MOD>;
        fn add(self, rhs: ModInt<MOD>) -> Self::Output {
            ModInt::new(self) + rhs
        }
    }
    impl<const MOD: i64> SubAssign<Self> for ModInt<MOD> {
        fn sub_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x - rhs.x);
        }
    }
    impl<const MOD: i64> Sub<ModInt<MOD>> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn sub(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x - rhs.x)
        }
    }
    impl<const MOD: i64> Sub<i64> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn sub(self, rhs: i64) -> Self::Output {
            self - ModInt::new(rhs)
        }
    }
    impl<const MOD: i64> Sub<ModInt<MOD>> for i64 {
        type Output = ModInt<MOD>;
        fn sub(self, rhs: ModInt<MOD>) -> Self::Output {
            ModInt::new(self) - rhs
        }
    }
    impl<const MOD: i64> MulAssign<Self> for ModInt<MOD> {
        fn mul_assign(&mut self, rhs: Self) {
            *self = ModInt::new(self.x * rhs.x);
        }
    }
    impl<const MOD: i64> Mul<ModInt<MOD>> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn mul(self, rhs: Self) -> Self::Output {
            ModInt::new(self.x * rhs.x)
        }
    }
    impl<const MOD: i64> Mul<i64> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn mul(self, rhs: i64) -> Self::Output {
            self * ModInt::new(rhs)
        }
    }
    impl<const MOD: i64> Mul<ModInt<MOD>> for i64 {
        type Output = ModInt<MOD>;
        fn mul(self, rhs: ModInt<MOD>) -> Self::Output {
            ModInt::new(self) * rhs
        }
    }
    impl<const MOD: i64> DivAssign<Self> for ModInt<MOD> {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
    impl<const MOD: i64> Div<ModInt<MOD>> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn div(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            ModInt::new(self.x * rhs.inverse().x)
        }
    }
    impl<const MOD: i64> Div<i64> for ModInt<MOD> {
        type Output = ModInt<MOD>;
        fn div(self, rhs: i64) -> Self::Output {
            self / ModInt::new(rhs)
        }
    }
    impl<const MOD: i64> Div<ModInt<MOD>> for i64 {
        type Output = ModInt<MOD>;
        fn div(self, rhs: ModInt<MOD>) -> Self::Output {
            ModInt::new(self) / rhs
        }
    }
    impl<const MOD: i64> From<usize> for ModInt<MOD> {
        fn from(x: usize) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl<const MOD: i64> From<i64> for ModInt<MOD> {
        fn from(x: i64) -> Self {
            ModInt::new(x)
        }
    }
    impl<const MOD: i64> From<i32> for ModInt<MOD> {
        fn from(x: i32) -> Self {
            ModInt::new(x as i64)
        }
    }
    impl<const MOD: i64> std::str::FromStr for ModInt<MOD> {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s.parse::<i64>() {
                Ok(x) => Ok(ModInt::from(x)),
                Err(e) => Err(e),
            }
        }
    }
    impl<const MOD: i64> std::iter::Sum for ModInt<MOD> {
        fn sum<I: Iterator<Item = ModInt<MOD>>>(iter: I) -> Self {
            let mut ret = Self::zero();
            for v in iter {
                ret += v;
            }
            ret
        }
    }
    #[allow(clippy::from_over_into)]
    impl<const MOD: i64> Into<usize> for ModInt<MOD> {
        fn into(self) -> usize {
            self.x as usize
        }
    }
    impl<const MOD: i64> fmt::Display for ModInt<MOD> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
    impl<const MOD: i64> fmt::Debug for ModInt<MOD> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }

    static mut MOD: i64 = 2;
    #[derive(Clone, Copy, Eq, Hash, PartialEq)]
    pub struct DynModInt {
        x: i64,
    }
    impl DynModInt {
        pub fn set_mod(val: i64) {
            unsafe {
                MOD = val;
            }
        }
        pub fn get_mod() -> i64 {
            unsafe { MOD }
        }
        pub fn val(&self) -> i64 {
            self.x
        }
        fn new(mut sig: i64) -> Self {
            if sig < 0 {
                let m = Self::get_mod();
                let ab = (-sig + m - 1) / m;
                sig += ab * m;
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
            let mut ret = Self::one();
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
    impl One for DynModInt {
        fn one() -> Self {
            Self { x: 1 }
        }
    }
    impl Zero for DynModInt {
        fn zero() -> Self {
            Self { x: 0 }
        }
        fn is_zero(&self) -> bool {
            self.x == 0
        }
        fn set_zero(&mut self) {
            self.x = 0;
        }
    }
    impl AddAssign<Self> for DynModInt {
        fn add_assign(&mut self, rhs: Self) {
            *self = DynModInt::new(self.x + rhs.x);
        }
    }
    impl Add<DynModInt> for DynModInt {
        type Output = DynModInt;
        fn add(self, rhs: Self) -> Self::Output {
            DynModInt::new(self.x + rhs.x)
        }
    }
    impl SubAssign<Self> for DynModInt {
        fn sub_assign(&mut self, rhs: Self) {
            *self = DynModInt::new(self.x - rhs.x);
        }
    }
    impl Sub<DynModInt> for DynModInt {
        type Output = DynModInt;
        fn sub(self, rhs: Self) -> Self::Output {
            DynModInt::new(self.x - rhs.x)
        }
    }
    impl MulAssign<Self> for DynModInt {
        fn mul_assign(&mut self, rhs: Self) {
            *self = DynModInt::new(self.x * rhs.x);
        }
    }
    impl Mul<DynModInt> for DynModInt {
        type Output = DynModInt;
        fn mul(self, rhs: Self) -> Self::Output {
            DynModInt::new(self.x * rhs.x)
        }
    }
    impl DivAssign<Self> for DynModInt {
        fn div_assign(&mut self, rhs: Self) {
            *self = *self / rhs;
        }
    }
    impl Div<DynModInt> for DynModInt {
        type Output = DynModInt;
        fn div(self, rhs: Self) -> Self::Output {
            #[allow(clippy::suspicious_arithmetic_impl)]
            DynModInt::new(self.x * rhs.inverse().x)
        }
    }
    impl From<usize> for DynModInt {
        fn from(x: usize) -> Self {
            DynModInt::new(x as i64)
        }
    }
    impl From<i64> for DynModInt {
        fn from(x: i64) -> Self {
            DynModInt::new(x)
        }
    }
    impl From<i32> for DynModInt {
        fn from(x: i32) -> Self {
            DynModInt::new(x as i64)
        }
    }
    impl std::str::FromStr for DynModInt {
        type Err = std::num::ParseIntError;
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            match s.parse::<i64>() {
                Ok(x) => Ok(DynModInt::from(x)),
                Err(e) => Err(e),
            }
        }
    }
    impl std::iter::Sum for DynModInt {
        fn sum<I: Iterator<Item = DynModInt>>(iter: I) -> Self {
            let mut ret = Self::zero();
            for v in iter {
                ret += v;
            }
            ret
        }
    }
    #[allow(clippy::from_over_into)]
    impl Into<usize> for DynModInt {
        fn into(self) -> usize {
            self.x as usize
        }
    }
    impl fmt::Display for DynModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
    impl fmt::Debug for DynModInt {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.x)
        }
    }
}
use modint::{DynModInt, ModInt};

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
            + MulAssign
            + DivAssign
            + Add<Output = T>
            + Mul<Output = T>
            + Div<Output = T>
            + Rem<Output = T>
            + Zero
            + One,
    > IntegerOperation for T
{
    fn into_primes(self) -> BTreeMap<T, usize> // O(N^0.5 x logN)
    {
        #[allow(clippy::eq_op)]
        if self == T::zero() {
            panic!("Zero has no divisors.");
        }
        #[allow(clippy::eq_op)]
        let two = T::one() + T::one();
        let three = two + T::one();
        let mut n = self;
        let mut ans = BTreeMap::new();
        while n % two == T::zero() {
            *ans.entry(two).or_insert(0) += 1;
            n /= two;
        }
        {
            let mut i = three;
            while i * i <= n {
                while n % i == T::zero() {
                    *ans.entry(i).or_insert(0) += 1;
                    n /= i;
                }
                i += two;
            }
        }
        if n != T::one() {
            *ans.entry(n).or_insert(0) += 1;
        }
        ans
    }
    fn into_divisors(self) -> Vec<T> // O(N^0.5)
    {
        if self == T::zero() {
            panic!("Zero has no primes.");
        }
        let n = self;
        let mut ret: Vec<T> = Vec::new();
        {
            let mut i = T::one();
            while i * i <= n {
                if n % i == T::zero() {
                    ret.push(i);
                    if i * i != n {
                        ret.push(n / i);
                    }
                }
                i += T::one();
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

mod convex_hull {
    use super::{ChangeMinMax, Rational};
    use std::collections::{BTreeMap, BTreeSet, VecDeque};
    pub struct ConvexHull {
        x_ys: BTreeMap<i64, Vec<i64>>,
    }
    impl ConvexHull {
        pub fn new() -> Self {
            Self {
                x_ys: BTreeMap::new(),
            }
        }
        pub fn add(&mut self, y: i64, x: i64) {
            self.x_ys.entry(x).or_insert(vec![]).push(y);
        }
        pub fn convex_hull(&self) -> Vec<(i64, i64)> {
            let mut x_ys = self
                .x_ys
                .iter()
                .map(|(x, ys)| (*x, ys.clone()))
                .collect::<Vec<_>>();
            // lower
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.sort();
            });
            let lower_yx = Self::weakly_monotone_tangents(&x_ys);
            // upper
            x_ys.iter_mut().for_each(|(_x, ys)| {
                ys.reverse();
            });
            x_ys.reverse();
            let upper_yx = Self::weakly_monotone_tangents(&x_ys);
            let mut ret = vec![];
            let mut seen = BTreeSet::new();
            for (y, x) in lower_yx.into_iter().chain(upper_yx.into_iter()) {
                if seen.contains(&(y, x)) {
                    continue;
                }
                ret.push((y, x));
                seen.insert((y, x));
            }
            ret
        }
        fn weakly_monotone_tangents(x_ys: &[(i64, Vec<i64>)]) -> VecDeque<(i64, i64)> {
            let mut vs = VecDeque::new();
            for (x, ys) in x_ys.iter() {
                let x = *x;
                let y = ys[0];
                if vs.is_empty() {
                    vs.push_back((y, x));
                    continue;
                }
                while vs.len() >= 2 {
                    let (y0, x0) = vs.pop_back().unwrap();
                    let (y1, x1) = vs.pop_back().unwrap();
                    let t0 = Rational::new(y0 - y, x0 - x);
                    let t1 = Rational::new(y1 - y, x1 - x);
                    if t0 < t1 {
                        vs.push_back((y1, x1));
                    } else {
                        vs.push_back((y1, x1));
                        vs.push_back((y0, x0));
                        break;
                    }
                }
                vs.push_back((y, x));
            }
            if let Some((x, ys)) = x_ys.last() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_back((y, x))
                }
            }
            if let Some((x, ys)) = x_ys.first() {
                let x = *x;
                for &y in ys.iter().skip(1) {
                    vs.push_front((y, x))
                }
            }
            vs
        }
    }
}
use convex_hull::ConvexHull;

mod matrix {
    use num::{One, Zero};
    use std::iter::Sum;
    use std::ops::{Add, Index, IndexMut, Mul, MulAssign, Sub};
    use std::slice::SliceIndex;
    #[derive(Clone)]
    pub struct Matrix<T> {
        h: usize,
        w: usize,
        vals: Vec<Vec<T>>,
    }
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
        Matrix<T>
    {
        pub fn new(h: usize, w: usize) -> Self {
            Self {
                h,
                w,
                vals: vec![vec![T::zero(); w]; h],
            }
        }
        pub fn identity(h: usize, w: usize) -> Self {
            debug_assert!(h == w);
            let mut vals = vec![vec![T::zero(); w]; h];
            for (y, line) in vals.iter_mut().enumerate() {
                for (x, val) in line.iter_mut().enumerate() {
                    *val = if y == x { T::one() } else { T::zero() };
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
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
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
                + One
                + Add<Output = T>
                + Sub<Output = T>
                + Mul
                + Sum<<T as Mul>::Output>
                + Zero
                + One,
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
    impl<T: Clone + Copy + One + Sub<Output = T> + Mul + Sum<<T as Mul>::Output> + Zero + One>
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
    use std::collections::{BinaryHeap, VecDeque};
    #[derive(Clone, Copy)]
    pub struct Edge {
        pub to: usize,
        pub rev_idx: usize, // index of paired edge at node "to".
        pub cap: i64,       // immutable capacity, s.t. flow <= cap
        pub flow: i64,      // flow can be negative.
        pub cost: i64,      // for min-cost flow
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
                cap,
                flow: 0,
                cost,
            });
            let rev_idx = self.g[from].len() - 1;
            self.g[to].push(Edge {
                to: from,
                rev_idx,
                cap: 0,
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
                    if level[edge.to].is_none() && (edge.flow < edge.cap) {
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
                    (edge.to, edge.rev_idx, edge.cap - edge.flow)
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
        pub fn min_cut_split(&self, src: usize) -> Vec<bool> {
            let nm = self.g.len() - 2;
            let mut split = vec![false; nm];
            let mut que = VecDeque::new();
            que.push_back(src);
            while let Some(v) = que.pop_front() {
                for e in self.g[v].iter() {
                    if e.flow >= e.cap || split[e.to] {
                        continue;
                    }
                    split[e.to] = true;
                    que.push_back(e.to);
                }
            }
            split
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
            if let Some(&(cost, flow)) = self.min_cost_slope_sub(src, dst, flow_lb, flow_ub).last()
            {
                if flow_lb <= flow && flow <= flow_ub {
                    return Some((cost, flow));
                }
            }
            None
        }
        pub fn min_cost_slope(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Vec<(i64, i64)> {
            self.min_cost_slope_sub(src, dst, flow_lb, flow_ub)
        }
        fn min_cost_slope_sub(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64,
            flow_ub: i64,
        ) -> Vec<(i64, i64)> {
            if self.flow_lb_sum == 0 {
                return self.min_cost_slope_impl(src, dst, flow_lb, flow_ub);
            }
            let dummy_src = self.g.len() - 2;
            let dummy_dst = self.g.len() - 1;
            // cyclic flow
            self.add_edge(dst, src, 1 << 60);
            let ds2dt_cost_flow =
                self.min_cost_slope_impl(dummy_src, dummy_dst, self.flow_lb_sum, self.flow_lb_sum);
            let s2t_cost_flow = self.min_cost_slope_impl(src, dst, flow_lb, flow_ub);
            s2t_cost_flow
                .into_iter()
                .zip(ds2dt_cost_flow.into_iter())
                .map(|((ds2dt_cost, _ds2dt_flow), (s2t_cost, s2t_flow))| {
                    (ds2dt_cost + s2t_cost, s2t_flow)
                })
                .collect::<Vec<_>>()
        }
        fn min_cost_slope_impl(
            &mut self,
            src: usize,
            dst: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            if self.neg_cost_any {
                self.min_negcost_slope(src, dst, flow_lb, flow_ub)
            } else {
                self.min_poscost_slope(src, dst, flow_lb)
            }
        }
        fn min_negcost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow
            flow_ub: i64, // upper bound flow
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
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
                            if e.flow >= e.cap {
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
                            delta_flow.chmin(e.cap - e.flow);
                            v = pv;
                        }
                    }
                    if delta_flow == 0 {
                        break;
                    }
                    min_cost += delta_flow * dist_sink;
                    flow_now += delta_flow;
                    slope.push((min_cost, flow_now));
                    {
                        let mut v = sink;
                        while let Some((pv, pei)) = prev[v] {
                            self.g[pv][pei].flow += delta_flow;
                            let rev_idx = self.g[pv][pei].rev_idx;
                            self.g[v][rev_idx].flow -= delta_flow;
                            v = pv;
                        }
                    }
                } else {
                    break;
                }

                dist.iter_mut().for_each(|x| *x = None);
                prev.iter_mut().for_each(|x| *x = None);
            }
            slope
        }
        fn min_poscost_slope(
            &mut self,
            source: usize,
            sink: usize,
            flow_lb: i64, // lower bound flow;
        ) -> Vec<(i64, i64)> {
            let mut slope = vec![];
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
                        if e.flow >= e.cap {
                            continue;
                        }
                        let nd = d + e.cost + h[v] - h[e.to];
                        if dist[e.to].chmin(nd) {
                            prev[e.to] = Some((v, ei));
                            que.push((Reverse(nd), e.to));
                        }
                    }
                }
                if dist[sink].is_none() {
                    break;
                }
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
                        delta_flow.chmin(e.cap - e.flow);
                        v = pv;
                    }
                }
                min_cost += delta_flow * h[sink];
                flow_now += delta_flow;
                slope.push((min_cost, flow_now));
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
            slope
        }
    }
}
use flow::Flow;

/*
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
*/

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

mod dynamic_connectivity {
    #[derive(Clone, Copy, PartialEq)]
    enum SplayDir {
        None = 0,
        Left,
        Right,
    }
    mod euler_step {
        use super::SplayDir;
        #[derive(Clone)]
        pub struct EulerStep {
            // splay
            pub left: *mut EulerStep,
            pub right: *mut EulerStep,
            pub parent: *mut EulerStep,
            // euler tour
            pub from: usize,
            pub to: usize,
            pub size: usize,
            pub at_this_level: bool,
            pub at_this_level_subany: bool,
            pub useless_connected: bool,
            pub useless_connected_subany: bool,
            // state
            value: i64,
            value_sum: i64,
        }
        impl EulerStep {
            pub fn new(from: usize, to: usize) -> Self {
                Self {
                    // splay
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    parent: std::ptr::null_mut(),
                    // euler tour
                    from,
                    to,
                    size: if from == to { 1 } else { 0 },
                    at_this_level: from < to,
                    at_this_level_subany: from < to,
                    useless_connected: false,
                    useless_connected_subany: false,
                    value: 0,
                    value_sum: 0,
                }
            }
            fn root(&mut self) -> *mut EulerStep {
                let mut t = self as *mut Self;
                unsafe {
                    while !(*t).parent.is_null() {
                        t = (*t).parent;
                    }
                }
                t
            }
            pub fn same(s: *mut Self, t: *mut Self) -> bool {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return false;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return false;
                }
                unsafe {
                    (*s).splay();
                    (*t).splay();
                    (*s).root() == (*t).root()
                }
            }
            pub fn update(&mut self) {
                self.size = if self.from == self.to { 1 } else { 0 };
                self.at_this_level_subany = self.at_this_level;
                self.useless_connected_subany = self.useless_connected;
                self.value_sum = self.value;
                let left = self.left;
                let right = self.right;
                unsafe {
                    if !left.is_null() {
                        self.size += (*left).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*left).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*left).useless_connected_subany;
                        self.value_sum += (*left).value_sum;
                    }
                    if !right.is_null() {
                        self.size += (*right).size;
                        self.at_this_level_subany =
                            self.at_this_level_subany || (*right).at_this_level_subany;
                        self.useless_connected_subany =
                            self.useless_connected_subany || (*right).useless_connected_subany;
                        self.value_sum += (*right).value_sum;
                    }
                }
            }
            pub fn splay(&mut self) {
                while self.for_parent() != SplayDir::None {
                    unsafe {
                        let p = self.parent;
                        let p_for_pp = (*p).for_parent();
                        if p_for_pp == SplayDir::None {
                            // zig
                            self.rotate();
                        } else if p_for_pp == self.for_parent() {
                            // zig zig
                            (*p).rotate();
                            self.rotate();
                        } else {
                            // zig zag
                            self.rotate();
                            self.rotate();
                        }
                    }
                }
            }
            fn for_parent(&mut self) -> SplayDir {
                if self.parent.is_null() {
                    SplayDir::None
                } else {
                    unsafe {
                        let me = self as *mut Self;
                        if (*self.parent).left == me {
                            SplayDir::Left
                        } else {
                            debug_assert!((*self.parent).right == me);
                            SplayDir::Right
                        }
                    }
                }
            }
            fn rotate(&mut self) {
                let p = self.parent;
                debug_assert!(!p.is_null());
                let me = self as *mut Self;
                unsafe {
                    debug_assert!((*me).for_parent() != SplayDir::None);
                    let pp = (*p).parent;
                    let c;
                    if (*me).for_parent() == SplayDir::Left {
                        c = (*me).right;
                        (*me).right = p;
                        (*p).left = c;
                    } else {
                        c = (*me).left;
                        (*me).left = p;
                        (*p).right = c;
                    }
                    if !pp.is_null() {
                        if (*pp).left == p {
                            (*pp).left = me;
                        } else {
                            (*pp).right = me;
                        }
                    }
                    (*me).parent = pp;
                    (*p).parent = me;
                    if !c.is_null() {
                        (*c).parent = p;
                    }
                    (*p).update();
                }
                self.update();
            }
            pub fn merge(mut s: *mut Self, mut t: *mut Self) -> *mut Self {
                if s.is_null() {
                    debug_assert!(!t.is_null());
                    return t;
                }
                if t.is_null() {
                    debug_assert!(!s.is_null());
                    return s;
                }
                unsafe {
                    s = (*s).root();
                    t = (*t).root();
                    while !(*s).right.is_null() {
                        s = (*s).right;
                    }
                    (*s).splay();
                    (*s).right = t;
                    (*t).parent = s;
                    (*s).update();
                }
                s
            }
            pub fn split(s: *mut Self) -> (*mut Self, *mut Self) // (..s, s..)
            {
                unsafe {
                    (*s).splay();
                    let t = (*s).left;
                    if !t.is_null() {
                        (*t).parent = std::ptr::null_mut();
                    }
                    (*s).left = std::ptr::null_mut();
                    (*s).update();
                    (t, s)
                }
            }
            pub fn set_value(&mut self, value: i64) {
                self.value = value;
            }
            pub fn get_value(&self) -> i64 {
                self.value
            }
            pub fn get_sum(&self) -> i64 {
                self.value_sum
            }
        }
    }
    mod euler_tree {
        use super::euler_step::EulerStep;
        use std::collections::HashMap;
        pub struct EulerTour {
            pub tour: Vec<HashMap<usize, Box<EulerStep>>>,
        }
        impl EulerTour {
            pub fn new(n: usize) -> Self {
                Self {
                    tour: (0..n)
                        .map(|i| {
                            let mut mp = HashMap::new();
                            mp.insert(i, Box::new(EulerStep::new(i, i)));
                            mp
                        })
                        .collect::<Vec<_>>(),
                }
            }
            pub fn get_node(&mut self, from: usize, to: usize) -> *mut EulerStep {
                self.tour[from]
                    .entry(to)
                    .or_insert_with(|| Box::new(EulerStep::new(from, to)));
                &mut **self.tour[from].get_mut(&to).unwrap()
            }
            #[allow(unused_assignments)]
            fn re_tour(s: *mut EulerStep) {
                let (s0, s1) = EulerStep::split(s);
                EulerStep::merge(s1, s0);
            }
            pub fn same(&mut self, a: usize, b: usize) -> bool {
                let a = self.get_node(a, a);
                let b = self.get_node(b, b);
                EulerStep::same(a, b)
            }
            #[allow(unused_assignments)]
            pub fn unite(&mut self, a: usize, b: usize) -> bool {
                if self.same(a, b) {
                    return false;
                }
                let aa = self.get_node(a, a);
                Self::re_tour(aa);
                let bb = self.get_node(b, b);
                Self::re_tour(bb);

                let ab = self.get_node(a, b);
                let ba = self.get_node(b, a);
                let aa_ab = EulerStep::merge(aa, ab);
                let bb_ba = EulerStep::merge(bb, ba);
                let _ = EulerStep::merge(aa_ab, bb_ba);
                true
            }
            fn remove_split(&mut self, from: usize, to: usize) -> (*mut EulerStep, *mut EulerStep) {
                let c = self.get_node(from, to);
                unsafe {
                    (*c).splay();
                    let left = (*c).left;
                    let right = (*c).right;
                    if !left.is_null() {
                        (*left).parent = std::ptr::null_mut();
                    }
                    if !right.is_null() {
                        (*right).parent = std::ptr::null_mut();
                    }
                    assert!(self.tour[from].remove(&to).is_some());
                    (left, right)
                }
            }
            pub fn cut(&mut self, a: usize, b: usize) -> bool {
                if !self.tour[a].contains_key(&b) {
                    return false;
                }
                let (xxa, bxx) = self.remove_split(a, b);
                if EulerStep::same(xxa, self.get_node(b, a)) {
                    let (xxb, _axxa) = self.remove_split(b, a);
                    let _ = EulerStep::merge(bxx, xxb);
                } else {
                    let (_bxxb, axx) = self.remove_split(b, a);
                    let _ = EulerStep::merge(axx, xxa);
                }
                true
            }
            pub fn get_size(&mut self, a: usize) -> usize {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.size
            }
            pub fn extract_level_match(t: *mut EulerStep) -> Option<(usize, usize)> {
                unsafe {
                    if t.is_null() || !(*t).at_this_level_subany {
                        return None;
                    }
                    if (*t).at_this_level {
                        (*t).splay();
                        (*t).at_this_level = false;
                        (*t).update();
                        return Some(((*t).from, (*t).to));
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_level_match(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_level_match(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn extract_useless_connected(t: *mut EulerStep) -> Option<usize> {
                unsafe {
                    if t.is_null() || !(*t).useless_connected_subany {
                        return None;
                    }
                    if (*t).useless_connected {
                        (*t).splay();
                        return Some((*t).from);
                    }
                    let left = (*t).left;
                    if let Some(ret) = Self::extract_useless_connected(left) {
                        return Some(ret);
                    }
                    let right = (*t).right;
                    if let Some(ret) = Self::extract_useless_connected(right) {
                        return Some(ret);
                    }
                    None
                }
            }
            pub fn update_useless_connected(&mut self, a: usize, b: bool) {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.useless_connected = b;
                node.update();
            }
            pub fn set_value(&mut self, a: usize, value: i64) {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.set_value(value);
                node.update();
            }
            pub fn get_value(&self, a: usize) -> i64 {
                self.tour[a][&a].get_value()
            }
            pub fn get_sum(&mut self, a: usize) -> i64 {
                let node = self.tour[a].get_mut(&a).unwrap();
                node.splay();
                node.get_sum()
            }
        }
    }
    use self::euler_step::EulerStep;
    use self::euler_tree::EulerTour;
    use std::collections::HashSet;
    pub struct DynamicConnectivity {
        n: usize,
        trees: Vec<EulerTour>,
        useless_edges: Vec<Vec<HashSet<usize>>>,
    }
    impl DynamicConnectivity {
        pub fn new(n: usize) -> Self {
            Self {
                n,
                trees: vec![EulerTour::new(n)],
                useless_edges: vec![vec![HashSet::new(); n]],
            }
        }
        pub fn unite(&mut self, a: usize, b: usize) -> bool {
            if a == b {
                return false;
            }
            if self.trees[0].unite(a, b) {
                return true;
            }
            assert!(self.useless_edges[0][a].insert(b));
            assert!(self.useless_edges[0][b].insert(a));
            if self.useless_edges[0][a].len() == 1 {
                self.trees[0].update_useless_connected(a, true);
            }
            if self.useless_edges[0][b].len() == 1 {
                self.trees[0].update_useless_connected(b, true);
            }
            false
        }
        pub fn same(&mut self, a: usize, b: usize) -> bool {
            self.trees[0].same(a, b)
        }
        pub fn cut(&mut self, a: usize, b: usize) -> bool {
            if a == b {
                return false;
            }
            self.trees
                .iter_mut()
                .zip(self.useless_edges.iter_mut())
                .for_each(|(tree, edges)| {
                    for (a, b) in [(a, b), (b, a)].iter().copied() {
                        if edges[a].remove(&b) && edges[a].is_empty() {
                            tree.update_useless_connected(a, false);
                        }
                    }
                });
            let org_level_len = self.trees.len();
            for level in (0..org_level_len).rev() {
                if self.trees[level].cut(a, b) {
                    // tree-connectivity changed.
                    if level == org_level_len - 1 {
                        self.trees.push(EulerTour::new(self.n));
                        self.useless_edges.push(vec![HashSet::new(); self.n]);
                    }
                    // try reconnect
                    self.trees.iter_mut().take(level).for_each(|tree| {
                        tree.cut(a, b);
                    });
                    return !self.reconstruct_connectivity(a, b, level);
                }
            }
            false
        }
        fn reconstruct_connectivity(&mut self, mut a: usize, mut b: usize, level: usize) -> bool {
            for i in (0..=level).rev() {
                if self.trees[i].get_size(a) > self.trees[i].get_size(b) {
                    std::mem::swap(&mut a, &mut b);
                }
                // edge update
                unsafe {
                    let node_a = self.trees[i].get_node(a, a);
                    (*node_a).splay();
                    while let Some((lup_a, lup_b)) = EulerTour::extract_level_match(node_a) {
                        self.trees[i + 1].unite(lup_a, lup_b);
                        (*node_a).splay();
                    }
                    // try_reconnect in euler tour
                    while let Some(x) = EulerTour::extract_useless_connected(node_a) {
                        while let Some(&y) = self.useless_edges[i][x].iter().next() {
                            for (x, y) in vec![(x, y), (y, x)].iter().copied() {
                                assert!(self.useless_edges[i][x].remove(&y));
                                if self.useless_edges[i][x].is_empty() {
                                    self.trees[i].update_useless_connected(x, false);
                                }
                            }
                            if self.trees[i].same(x, y) {
                                for (x, y) in [(x, y), (y, x)].iter().copied() {
                                    self.useless_edges[i + 1][x].insert(y);
                                    if self.useless_edges[i + 1][x].len() == 1 {
                                        self.trees[i + 1].update_useless_connected(x, true);
                                    }
                                }
                            } else {
                                for j in 0..=i {
                                    self.trees[j].unite(x, y);
                                }
                                return true;
                            }
                        }
                        (*node_a).splay();
                    }
                }
            }
            false
        }
        pub fn set_value(&mut self, x: usize, value: i64) {
            self.trees[0].set_value(x, value);
        }
        pub fn get_value(&self, x: usize) -> i64 {
            self.trees[0].get_value(x)
        }
        pub fn get_sum(&mut self, x: usize) -> i64 {
            self.trees[0].get_sum(x)
        }
    }
    fn get_level_num(dynamic_connectivity: &DynamicConnectivity) -> usize {
        dynamic_connectivity.trees.len()
    }
    #[cfg(test)]
    mod tests {
        use crate::dynamic_connectivity::get_level_num;

        use super::DynamicConnectivity;
        use rand::{Rng, SeedableRng};
        use rand_chacha::ChaChaRng;
        use std::collections::{BTreeSet, VecDeque};
        fn assign_group_ids(g: &[BTreeSet<usize>]) -> Vec<usize> {
            let n = g.len();
            let mut ids = vec![0; n];
            let mut id_cnt = 0;
            for i in 0..n {
                if ids[i] > 0 {
                    continue;
                }
                id_cnt += 1;
                let id = id_cnt;
                let mut que = VecDeque::new();
                que.push_back(i);
                while let Some(v) = que.pop_front() {
                    ids[v] = id;
                    for nv in g[v].iter().copied() {
                        if ids[nv] > 0 {
                            assert!(ids[nv] == id);
                            continue;
                        }
                        que.push_back(nv);
                    }
                }
            }
            ids
        }
        fn trial(n: usize, ques: Vec<(usize, usize, usize)>) {
            let mut dc = DynamicConnectivity::new(n);
            let mut g = vec![BTreeSet::new(); n];
            let mut log_n = 1usize;
            while 2usize.pow(log_n as u32) < n {
                log_n += 1;
            }
            for (t, a, b) in ques {
                match t {
                    0 => {
                        dc.unite(a, b);
                        g[a].insert(b);
                        g[b].insert(a);
                    }
                    1 => {
                        dc.cut(a, b);
                        g[a].remove(&b);
                        g[b].remove(&a);
                    }
                    _ => unreachable!(),
                }
                let ids = assign_group_ids(&g);
                for j in 0..n {
                    for i in 0..j {
                        assert_eq!(dc.same(i, j), ids[i] == ids[j]);
                    }
                }
                assert!(get_level_num(&dc) <= log_n);
            }
        }
        #[test]
        fn random_test() {
            let n = 10;
            let mut rng = ChaChaRng::from_seed([0; 32]);
            for _ in 0..1000 {
                let ques = {
                    let mut es = BTreeSet::new();
                    let mut ques = vec![];
                    while ques.len() < n * n {
                        let t = rng.gen::<usize>() % 2;
                        let mut a = rng.gen::<usize>() % n;
                        let mut b = (a + 1 + rng.gen::<usize>() % (n - 1)) % n;
                        if a > b {
                            std::mem::swap(&mut a, &mut b);
                        }
                        match t {
                            0 => {
                                if es.contains(&(a, b)) {
                                    continue;
                                }
                                es.insert((a, b));
                                ques.push((t, a, b));
                            }
                            1 => {
                                if !es.contains(&(a, b)) {
                                    continue;
                                }
                                es.remove(&(a, b));
                                ques.push((t, a, b));
                            }
                            _ => unreachable!(),
                        }
                    }
                    ques
                };
                trial(n, ques);
            }
        }
    }
}
use dynamic_connectivity::DynamicConnectivity;

mod pair {
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    pub struct Pair<TA, TB> {
        a: TA,
        b: TB,
    }
    impl<TA: Clone + Copy, TB: Clone + Copy> Pair<TA, TB> {
        pub fn from(a: TA, b: TB) -> Self {
            Self { a, b }
        }
    }
    impl<TA: AddAssign, TB: AddAssign> AddAssign for Pair<TA, TB> {
        fn add_assign(&mut self, rhs: Self) {
            self.a += rhs.a;
            self.b += rhs.b;
        }
    }
    impl<TA: Add<Output = TA>, TB: Add<Output = TB>> Add for Pair<TA, TB> {
        type Output = Self;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                a: self.a + rhs.a,
                b: self.b + rhs.b,
            }
        }
    }
    impl<TA: SubAssign, TB: SubAssign> SubAssign for Pair<TA, TB> {
        fn sub_assign(&mut self, rhs: Self) {
            self.a -= rhs.a;
            self.b -= rhs.b;
        }
    }
    impl<TA: Sub<Output = TA>, TB: Sub<Output = TB>> Sub for Pair<TA, TB> {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                a: self.a - rhs.a,
                b: self.b - rhs.b,
            }
        }
    }
    impl<TA: Neg<Output = TA>, TB: Neg<Output = TB>> Neg for Pair<TA, TB> {
        type Output = Self;
        fn neg(self) -> Self::Output {
            Self {
                a: -self.a,
                b: -self.b,
            }
        }
    }
    impl<T: Clone + Copy, TA: MulAssign<T> + Clone + Copy, TB: MulAssign<T> + Clone + Copy>
        MulAssign<T> for Pair<TA, TB>
    {
        fn mul_assign(&mut self, rhs: T) {
            self.a *= rhs;
            self.b *= rhs;
        }
    }
    impl<
            T: Clone + Copy,
            TA: Mul<T, Output = TA> + Clone + Copy,
            TB: Mul<T, Output = TB> + Clone + Copy,
        > Mul<T> for Pair<TA, TB>
    {
        type Output = Self;
        fn mul(self, rhs: T) -> Self::Output {
            Self {
                a: self.a * rhs,
                b: self.b * rhs,
            }
        }
    }
    impl<T: Clone + Copy, TA: DivAssign<T> + Clone + Copy, TB: DivAssign<T> + Clone + Copy>
        DivAssign<T> for Pair<TA, TB>
    {
        fn div_assign(&mut self, rhs: T) {
            self.a /= rhs;
            self.b /= rhs;
        }
    }
    impl<
            T: Clone + Copy,
            TA: Div<T, Output = TA> + Clone + Copy,
            TB: Div<T, Output = TB> + Clone + Copy,
        > Div<T> for Pair<TA, TB>
    {
        type Output = Self;
        fn div(self, rhs: T) -> Self::Output {
            Self {
                a: self.a / rhs,
                b: self.b / rhs,
            }
        }
    }
}
use pair::Pair;

mod deletable_binary_heap {
    use std::collections::BinaryHeap;
    #[derive(Clone)]
    pub struct DeletableBinaryHeap<T> {
        que: BinaryHeap<T>,
        del_rsv: BinaryHeap<T>,
    }
    impl<T: Clone + PartialOrd + Ord> DeletableBinaryHeap<T> {
        pub fn new() -> Self {
            Self {
                que: BinaryHeap::<T>::new(),
                del_rsv: BinaryHeap::<T>::new(),
            }
        }
        pub fn pop(&mut self) -> Option<T> {
            self.lazy_eval();
            self.que.pop()
        }
        pub fn push(&mut self, v: T) {
            self.lazy_eval();
            self.que.push(v)
        }
        pub fn peek(&mut self) -> Option<&T> {
            self.lazy_eval();
            self.que.peek()
        }
        pub fn remove(&mut self, del_v: &T) {
            self.del_rsv.push(del_v.clone());
            debug_assert!(self.que.iter().any(|v| v == del_v));
        }
        fn lazy_eval(&mut self) {
            while let Some(del_v) = self.del_rsv.peek() {
                if let Some(v) = self.que.peek() {
                    if del_v == v {
                        self.que.pop();
                        self.del_rsv.pop();
                    } else {
                        break;
                    }
                } else {
                    unreachable!()
                }
            }
        }
    }
}
use deletable_binary_heap::DeletableBinaryHeap;

mod point {
    use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
    #[derive(Clone, Copy)]
    pub struct Point<T> {
        pub y: T,
        pub x: T,
    }
    impl<T: Clone> Point<T> {
        pub fn new(y: T, x: T) -> Self {
            Self { y, x }
        }
    }
    impl<T: Add<Output = T>> Add for Point<T> {
        type Output = Point<T>;
        fn add(self, rhs: Self) -> Self::Output {
            Self {
                y: self.y.add(rhs.y),
                x: self.x.add(rhs.x),
            }
        }
    }
    impl<T: AddAssign> AddAssign for Point<T> {
        fn add_assign(&mut self, rhs: Self) {
            self.y.add_assign(rhs.y);
            self.x.add_assign(rhs.x);
        }
    }
    impl<T: Sub<Output = T>> Sub for Point<T> {
        type Output = Point<T>;
        fn sub(self, rhs: Self) -> Self::Output {
            Self {
                y: self.y.sub(rhs.y),
                x: self.x.sub(rhs.x),
            }
        }
    }
    impl<T: SubAssign> SubAssign for Point<T> {
        fn sub_assign(&mut self, rhs: Self) {
            self.y.sub_assign(rhs.y);
            self.x.sub_assign(rhs.x);
        }
    }
    impl<T: Clone + Mul<Output = T>> Mul<T> for Point<T> {
        type Output = Self;
        fn mul(self, rhs: T) -> Self::Output {
            Self {
                y: self.y.mul(rhs.clone()),
                x: self.x.mul(rhs),
            }
        }
    }
    impl<T: Clone + Div<Output = T>> Div<T> for Point<T> {
        type Output = Self;
        fn div(self, rhs: T) -> Self::Output {
            Self {
                y: self.y.div(rhs.clone()),
                x: self.x.div(rhs),
            }
        }
    }
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

fn main() {
    solver::Solver::new().solve();
}

mod solver {
    use super::*;

    const LEFT: usize = 0;
    const RIGHT: usize = 1;
    const LOWER: usize = 2;
    const UPPER: usize = 3;
    mod rect {
        use super::*;
        #[derive(Clone, Copy, PartialEq, Eq)]
        pub struct Rect {
            pub y0: usize,
            pub x0: usize,
            pub y1: usize,
            pub x1: usize,
        }
        impl Rect {
            pub fn from_point(y: usize, x: usize) -> Self {
                Self {
                    y0: y,
                    x0: x,
                    y1: y + 1,
                    x1: x + 1,
                }
            }
            pub fn new(y0: usize, x0: usize, y1: usize, x1: usize) -> Self {
                debug_assert!(y0 <= y1);
                debug_assert!(x0 <= x1);
                Self { y0, x0, y1, x1 }
            }
            #[inline(always)]
            pub fn area(&self) -> usize {
                (self.y1 - self.y0) * (self.x1 - self.x0)
            }
            #[inline(always)]
            fn is_right(&self, rhs: &Self) -> bool {
                self.x1 <= rhs.x0 && self.y0 < rhs.y1 && rhs.y0 < self.y1
            }
            #[inline(always)]
            fn is_left(&self, rhs: &Self) -> bool {
                rhs.x1 <= self.x0 && self.y0 < rhs.y1 && rhs.y0 < self.y1
            }
            #[inline(always)]
            fn is_lower(&self, rhs: &Self) -> bool {
                rhs.y1 <= self.y0 && self.x0 < rhs.x1 && rhs.x0 < self.x1
            }
            #[inline(always)]
            fn is_upper(&self, rhs: &Self) -> bool {
                self.y1 <= rhs.y0 && self.x0 < rhs.x1 && rhs.x0 < self.x1
            }
            #[inline(always)]
            pub fn right_dist(&self, rhs: &Self) -> Option<usize> {
                if self.is_right(rhs) {
                    Some(rhs.x0 - self.x1)
                } else {
                    None
                }
            }
            #[inline(always)]
            pub fn left_dist(&self, rhs: &Self) -> Option<usize> {
                if self.is_left(rhs) {
                    Some(self.x0 - rhs.x1)
                } else {
                    None
                }
            }
            #[inline(always)]
            pub fn upper_dist(&self, rhs: &Self) -> Option<usize> {
                if self.is_upper(rhs) {
                    Some(rhs.y0 - self.y1)
                } else {
                    None
                }
            }
            #[inline(always)]
            pub fn lower_dist(&self, rhs: &Self) -> Option<usize> {
                if self.is_lower(rhs) {
                    Some(self.y0 - rhs.y1)
                } else {
                    None
                }
            }
        }
    }
    use rect::Rect;
    pub struct Solver {
        t0: Instant,
        w: usize,
        d: usize,
        n: usize,
        a: Vec<Vec<usize>>,
        divs: Vec<Vec<Vec<(usize, usize)>>>,
    }
    impl Solver {
        pub fn new() -> Self {
            let t0 = Instant::now();
            let w = read::<usize>();
            let d = read::<usize>();
            let n = read::<usize>();
            let a = read_mat::<usize>(d, n);
            let divs = a
                .iter()
                .map(|a| {
                    a.iter()
                        .map(|&a| {
                            let mut hws = vec![];
                            for (y, x) in (1..=w)
                                .take_while(|&y| y * y <= a)
                                .map(|y| (y, (a + y - 1) / y))
                                .filter(|&(_y, x)| x <= w)
                            {
                                hws.push((y, x));
                                if y != x {
                                    hws.push((x, y));
                                }
                            }
                            hws.sort();
                            hws
                        })
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            Self {
                t0,
                w,
                d,
                n,
                a,
                divs,
            }
        }
        fn pyramid(&self, _a: &[usize], divs: &[Vec<(usize, usize)>]) -> Vec<Rect> {
            let mut right_y0x0 = BTreeMap::new();
            let mut rects = vec![];
            let mut rems = vec![];
            // from right top
            {
                let mut y1 = self.w;
                let mut lim_bw = self.w;
                for divs in divs.iter().rev() {
                    // from big to small
                    let mut ok = false;
                    for &(bh, bw) in divs.iter().filter(|&&(_bh, bw)| bw <= lim_bw) {
                        if y1 < bh {
                            continue;
                        }
                        let y0 = y1 - bh;
                        let x1 = self.w; // fixed
                        let x0 = x1 - bw;
                        let rect = Rect::new(y0, x0, y1, x1);
                        debug_assert!(rect.y0.clamp(0, self.w) == rect.y0);
                        debug_assert!(rect.x0.clamp(0, self.w) == rect.x0);
                        debug_assert!(rect.y1.clamp(0, self.w) == rect.y1);
                        debug_assert!(rect.x1.clamp(0, self.w) == rect.x1);
                        rects.push(rect);
                        right_y0x0.insert(y0, x0);
                        lim_bw.chmin(bw);
                        if rems.is_empty() {
                            rems.push((y1, x0, RIGHT));
                        }
                        rems.push((y0, x0, RIGHT));
                        ok = true;
                        y1 = y0;
                        break;
                    }
                    if !ok {
                        break;
                    }
                }
                if !right_y0x0.contains_key(&0) {
                    right_y0x0.insert(0, self.w);
                }
            }
            let right_y0x0 = right_y0x0;
            // from left bottom
            if rects.len() < divs.len() {
                {
                    let mut y0 = 0;
                    for divs in divs.iter().rev().skip(rects.len()) {
                        let mut ok = false;
                        for &(bh, bw) in divs.iter() {
                            let y1 = y0 + bh;
                            if y1 > self.w {
                                break;
                            }
                            let x0 = 0; // fixed
                            let x1 = bw;
                            let (_, &lim_x1) = right_y0x0.less_than(&y1).unwrap();
                            if lim_x1 < x1 {
                                continue;
                            }
                            let rect = Rect::new(y0, x0, y1, x1);
                            debug_assert!(rect.y0.clamp(0, self.w) == rect.y0);
                            debug_assert!(rect.x0.clamp(0, self.w) == rect.x0);
                            debug_assert!(rect.y1.clamp(0, self.w) == rect.y1);
                            debug_assert!(rect.x1.clamp(0, self.w) == rect.x1);
                            rects.push(rect);
                            rems.push((y0, x1, LEFT));
                            ok = true;
                            y0 = y1;
                            break;
                        }
                        if !ok {
                            break;
                        }
                    }
                    if y0 < self.w {
                        rems.push((y0, 0, LEFT));
                    }
                }
                let mut cands = vec![];
                // ascending order from last
                rems.sort_by_cached_key(|(y, _x, _lr)| Reverse(*y));
                let mut x0 = 0;
                let mut x1 = self.w;
                let mut y0 = 0;
                while let Some((y1, x, lr)) = rems.pop() {
                    let dh = y1 - y0;
                    let dw = x1 - x0;
                    if dh > 0 && dw > 0 {
                        cands.push(Rect::new(y0, x0, y1, x1));
                        if cands.len() >= divs.len() {
                            break;
                        }
                    }
                    if lr == LEFT {
                        x0 = x;
                    } else if lr == RIGHT {
                        x1 = x;
                    } else {
                        unreachable!()
                    }
                    y0 = y1;
                }
                cands.sort_by_cached_key(|rect| rect.area());
                for rect in cands.iter().rev().take(divs.len() - rects.len()) {
                    debug_assert!(rect.y0.clamp(0, self.w) == rect.y0);
                    debug_assert!(rect.x0.clamp(0, self.w) == rect.x0);
                    debug_assert!(rect.y1.clamp(0, self.w) == rect.y1);
                    debug_assert!(rect.x1.clamp(0, self.w) == rect.x1);
                    rects.push(rect.clone());
                }
            }
            debug_assert!(rects.len() == divs.len());
            rects
        }
        pub fn solve(&self) {
            let mut ans = vec![];
            for (a, divs) in self.a.iter().zip(self.divs.iter()) {
                let rects = self.pyramid(a, divs);
                ans.push(rects);
            }
            self.answer(ans);
        }
        fn answer(&self, rects: Vec<Vec<Rect>>) {
            for mut rects in rects {
                rects.sort_by_cached_key(|r| r.area());
                for rect in rects {
                    debug_assert!(rect.y0.clamp(0, self.w) == rect.y0);
                    debug_assert!(rect.x0.clamp(0, self.w) == rect.x0);
                    debug_assert!(rect.y1.clamp(0, self.w) == rect.y1);
                    debug_assert!(rect.x1.clamp(0, self.w) == rect.x1);
                    println!("{} {} {} {}", rect.y0, rect.x0, rect.y1, rect.x1);
                }
            }
        }
    }
}
