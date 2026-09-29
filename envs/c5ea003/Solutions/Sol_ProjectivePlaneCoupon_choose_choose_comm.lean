-- Prove2me | solution 1 for ProjectivePlaneCoupon.choose_choose_comm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:08:36.781985+00:00
-- url     : https://prove2.me/submissions/30d75aa2-3ba5-4f2a-b165-c9165ac453c8

-- Sol generated from MachineLearning/ProjectivePlaneCoupon/Slowness.lean
import Mathlib
import Definitions.Def_MachineLearning_ProjectivePlaneCoupon_Slowness
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Projective-plane coupon collection is slower than uniform: the structural engine

Fix a prime power `q ≥ 2` and a projective plane of order `q`.  It has
`n = q² + q + 1` points and the same number of lines; every line is a
`(q+1)`-subset of points, every point lies on `q+1` lines, and any two
distinct points lie on a unique common line.

We study two coupon-collection mechanisms on the `n` points:

* **plane mechanism** — each draw is a uniformly random *line* (one of the
  `n` lines), revealing the `q+1` points on it;
* **uniform mechanism** — each draw is a uniformly random `(q+1)`-subset of
  the `n` points.

For a covering process whose single-draw probability of *avoiding* a fixed set
`A` is `p_A`, the expected time to cover everything is the inclusion–exclusion
sum `E = Σ_{∅ ≠ A} (-1)^{|A|+1} / (1 - p_A)`.  The Grünbaum–Yaakobi question
(disproved for `q = 2`, the Fano plane) asks whether the plane mechanism is
*slower*, i.e. has the larger `E`.  The general statement (all prime powers)
is open; this file isolates the structural mechanism that drives it.

## Avoid-probabilities

For a single draw, `p_A = (number of draws avoiding A) / (number of draws)`.

* Uniform: `p_A` depends only on `k = |A|`, namely
  `uAvoid q k = C(n-k, q+1) / C(n, q+1) = ∏_{i<k}(q² - i) / ∏_{i<k}(n - i)`
  (the falling-factorial form, with `n - (q+1) = q²`).
* Plane: `p_A` depends on the *geometry* of `A`.  A single point is missed by
  `q²` lines (`pPoint`); a pair by `q² - q` (`pPair`); a **collinear** triple by
  `q² - 2q` (`pColl`); a **generic** (non-collinear) triple by `(q-1)²`
  (`pGen`).

## Main results

* `meanMatch` — the **mean-matching identity** (a binomial subset-of-a-subset
  identity): averaged over all `k`-subsets, the plane mechanism avoids a set
  with exactly the uniform probability.  This is why low orders agree.
* `match1`, `match2` — at orders `1` and `2` *every* subset is geometrically
  equivalent, so the plane and uniform avoid-probabilities coincide *exactly*;
  hence the `E`-contributions of orders `1` and `2` are identical.
* `jensen2` — strict two-point Jensen inequality for `x ↦ 1/(1-x)`.
* `slowness3` — at order `3` the plane mechanism splits a single uniform value
  into two distinct ones (`pColl ≠ pGen`) **with the same mean**, so by strict
  convexity its order-`3` contribution to `E` is strictly larger.  This is the
  first order at which the two mechanisms diverge, and it diverges in the
  "slower" direction.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The plane mechanism is slower for *every* prime
  power `q`.  Bolder: the divergence is forced entirely by collinearity — the
  two mechanisms agree to all orders "on average", and disagree pointwise for
  the first time at triples, where convexity of `1/(1-p)` makes the spread-out
  plane values cost strictly more.
Experiment (Experimenter): (1) Proved the binomial identity
  `C(n,k)·C(n-k,q+1) = C(n,q+1)·C(n-(q+1),k)` from factorials — this is exactly
  "mean of plane avoid-prob over k-sets = uniform avoid-prob". (2) Proved the
  exact pointwise equalities at orders 1,2 (`match1`,`match2`). (3) Proved the
  order-3 weighted-mean identity `match3` and combined it with a freshly proved
  strict Jensen lemma `jensen2` to get `slowness3`.  Computationally verified
  the *full* `E`-inequality for `q = 2,3` (see `FanoEvidence.lean` and
  `ComputationalEvidence.md`).
Analysis (Analyst): The number of collinear triples is `n·C(q+1,3)`; the rest
  are generic.  Their avoid-counts differ by exactly one line
  (`(q-1)² - (q²-2q) = 1`), so `pColl ≠ pGen` always.  The clean factorization
  `#generic·6 = n·q³(q+1)` (used in `slowness3`) shows generic triples dominate,
  so the plane really does carry two genuinely different values at order 3.
  "True but hard": the full all-orders statement needs control of the
  alternating tail (orders `≥ 4`), which is why only `q = 2,3,4,5` are known.
Critique (Critic): `slowness3` is a genuine strict inequality (uses `jensen2`,
  itself proved by `nlinarith` on `(x-y)² > 0`), not `decide`/`native_decide`.
  The geometric avoid-counts are taken as definitions; their correctness is
  cross-checked against the explicit Fano plane in `FanoEvidence.lean`.
Synthesis (PI): Orders 1–2 contribute equally; order 3 strictly favours the
  plane (slower).  The open problem is exactly the sign-controlled tail.
-/

open Nat Finset

open ProjectivePlaneCoupon





/-! ### The binomial subset-of-a-subset identity (mean-matching) -/



/-! ### Avoid-probabilities -/










/-! ### Orders 1 and 2: the mechanisms agree exactly -/



/-! ### Order 3: the weighted-mean identity and the strict divergence -/





open ProjectivePlaneCoupon in
theorem solution(n k j : ℕ) (h : k + j ≤ n) :
    n.choose k * (n - k).choose j = n.choose j * (n - j).choose k := by
  have hk : k ≤ n := le_trans (Nat.le_add_right k j) h
  have hj : j ≤ n := le_trans (Nat.le_add_left j k) h
  have hjk : j ≤ n - k := by omega
  have hkj : k ≤ n - j := by omega
  have W : 0 < k ! * j ! * (n - k - j)! := by positivity
  apply Nat.eq_of_mul_eq_mul_right W
  have a1 := Nat.choose_mul_factorial_mul_factorial hk
  have a1' := Nat.choose_mul_factorial_mul_factorial hj
  have a2 : (n - k).choose j * j ! * ((n - k) - j)! = (n - k)! :=
    Nat.choose_mul_factorial_mul_factorial hjk
  have a3 : (n - j).choose k * k ! * ((n - j) - k)! = (n - j)! :=
    Nat.choose_mul_factorial_mul_factorial hkj
  have enj : (n - k) - j = n - k - j := by omega
  have enk : (n - j) - k = n - k - j := by omega
  rw [enj] at a2; rw [enk] at a3
  have lhs : n.choose k * (n - k).choose j * (k ! * j ! * (n - k - j)!) = n ! := by
    have e : n.choose k * (n - k).choose j * (k ! * j ! * (n - k - j)!)
        = (n.choose k * k !) * ((n - k).choose j * j ! * (n - k - j)!) := by ring
    rw [e, a2]; exact a1
  have rhs : n.choose j * (n - j).choose k * (k ! * j ! * (n - k - j)!) = n ! := by
    have e : n.choose j * (n - j).choose k * (k ! * j ! * (n - k - j)!)
        = (n.choose j * j !) * ((n - j).choose k * k ! * (n - k - j)!) := by ring
    rw [e, a3]; exact a1'
  rw [lhs, rhs]
