-- Prove2me | solution 1 for TraceDistribution.binom_powerSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T19:19:47.718484+00:00
-- url     : https://prove2.me/submissions/9e295f5d-b28f-497b-957e-452a48d44d76

-- Sol generated from Logic/TraceDistribution/Sharpness.lean
import Mathlib
import Definitions.Def_Logic_TraceDistribution_Sharpness
/-
# The power-sum threshold is exactly optimal

`Logic.TraceDistribution.PowerSums` shows that a multiset of naturals with all values
`< n` (equivalently, with joint support of size `≤ n`) is determined by its power sums
`p_0, …, p_{n-1}`.  This file proves that this threshold cannot be lowered by even one
degree, by an explicit construction:

`binomEven n` and `binomOdd n` are the *even* and *odd* parts of the `n`-th alternating
binomial (finite-difference) measure on `{0, 1, …, n}`, i.e.

  `binomEven n = ⨄_{k ≤ n, n-k even} C(n,k) copies of k`,
  `binomOdd  n = ⨄_{k ≤ n, n-k odd } C(n,k) copies of k`.

Because the `n`-th forward difference annihilates every polynomial of degree `< n`, the
two multisets have *identical* power sums `p_0, …, p_{n-1}`, while they differ (the
value `n` occurs once in the first and never in the second).  Both have all values
`≤ n` and joint support exactly `{0, …, n}`, of size `n + 1`.

Combining with `multiset_eq_of_powerSum_eq` this pins the threshold exactly:

* `powerSum_rigidity_at_threshold` — `n + 1` power sums suffice;
* `powerSum_rigidity_fails_below_threshold` — `n` power sums do not.

This is the *cross-domain* half of the trace-distribution story: rigidity comes from
Lagrange interpolation (linear algebra over `ℚ`), and the exact failure boundary comes
from the calculus of finite differences (the binomial transform).

## Lab notes (experimental data)

`n = 2`: `binomEven 2 = {0, 2}` (`k = 0, 2`), `binomOdd 2 = {1, 1}`.
  `p_0 : 2 = 2`,  `p_1 : 2 = 2`,  `p_2 : 4 ≠ 2`.  Threshold `n + 1 = 3` is needed.
`n = 3`: `binomEven 3 = {1,1,1,3}`, `binomOdd 3 = {0,2,2,2}`.
  `p_0 : 4 = 4`,  `p_1 : 6 = 6`,  `p_2 : 12 = 12`,  `p_3 : 30 ≠ 24`.
`n = 4`: `binomEven 4 = {0,2,2,2,2,2,2,4}`, `binomOdd 4 = {1,1,1,1,3,3,3,3}`.
  `p_0 = 8 = 8`, `p_1 = 16 = 16`, `p_2 = 40 = 40`, `p_3 = 112 = 112`, `p_4 = 352 ≠ 328`.
`n = 5`: `p_0 … p_4` all agree (`16, 40, 120, 400, 1440`), and `p_5 : 5560 ≠ 5440`.

The top-degree gaps are `4-2 = 2`, `30-24 = 6`, `352-328 = 24`, `5560-5440 = 120`, i.e.
exactly `n !` (OEIS A000142).  This is proved in general as `binom_powerSum_top_gap`,
so the two multisets are not merely different — the discrepancy is the factorial.
-/

open Finset

open TraceDistribution

/-! ## A multiset built from a multiplicity function -/


theorem powerSum_replicateSum (s : Finset ℕ) (c : ℕ → ℕ) (j : ℕ) :
    (Multiset.map (fun a => a ^ j) (replicateSum s c)).sum = ∑ k ∈ s, c k * k ^ j := by
  classical
  unfold replicateSum
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih,
        Multiset.map_replicate, Multiset.sum_replicate, smul_eq_mul]



/-! ## The alternating binomial pair -/



/-- The `n`-th finite difference kills `x ↦ x^j` for `j < n`: in explicit binomial form,
`∑_{k=0}^{n} (-1)^{n-k} C(n,k) k^j = 0`. -/
theorem alternating_binomial_pow (n j : ℕ) (hj : j < n) :
    ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * (n.choose k)) * (k : ℤ) ^ j = 0 := by
  have h := fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) (j := j) (n := n) hj
  have h0 := congrFun h 0
  rw [fwdDiff_iter_eq_sum_shift] at h0
  simpa using h0








/-! ## The exact threshold -/





open TraceDistribution in
theorem solution(n j : ℕ) (hj : j < n) :
    (Multiset.map (fun a => a ^ j) (binomEven n)).sum
      = (Multiset.map (fun a => a ^ j) (binomOdd n)).sum := by
  rw [binomEven, binomOdd, powerSum_replicateSum, powerSum_replicateSum]
  have key : ((∑ k ∈ range (n + 1), (if Even (n - k) then n.choose k else 0) * k ^ j : ℕ) : ℤ)
      = ((∑ k ∈ range (n + 1), (if Even (n - k) then 0 else n.choose k) * k ^ j : ℕ) : ℤ) := by
    push_cast
    have hstep : ∀ k ∈ range (n + 1),
        (if Even (n - k) then ((n.choose k : ℤ)) else 0) * (k : ℤ) ^ j
          = ((-1 : ℤ) ^ (n - k) * (n.choose k)) * (k : ℤ) ^ j
            + (if Even (n - k) then (0 : ℤ) else (n.choose k : ℤ)) * (k : ℤ) ^ j := by
      intro k _
      by_cases hE : Even (n - k)
      · simp [hE, hE.neg_one_pow]
      · rw [Nat.not_even_iff_odd] at hE
        simp [Nat.not_even_iff_odd.mpr hE, hE.neg_one_pow]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib,
      alternating_binomial_pow n j hj, zero_add]
  exact_mod_cast key
