-- Prove2me | solution 1 for HyperbolicBerggrenGeodesics.no_universal_depth_cfSum_law
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:02:59.720776+00:00
-- url     : https://prove2.me/submissions/a488ea20-c614-4fb6-b98f-8cfd9ab35872

-- Sol generated from Geometry/HyperbolicBerggrenTreeDepth.lean
import Mathlib
import Definitions.Def_Geometry_HyperbolicBerggrenGeodesics
import Definitions.Def_Geometry_HyperbolicBerggrenTreeDepth
import Theorems.Thm_HyperbolicBerggrenGeodesics_cfSum_consec

/-!
# Hyperbolic–Pythagorean Geodesics, cycle VIII: the tree structure of the depth function

Cycles I–VII studied a *single* Berggren node `(m,n)` and the effect of one Berggren move
on its hyperbolic position.  The quantity that the mission statement is really about — the
**path length**, i.e. the combinatorial depth `k` at which a node occurs — was so far only
touched in the negative (`depth_not_bounded_by_distance`: depth is not bounded by a constant
multiple of the hyperbolic distance).  This file settles the positive half and the
book-keeping that makes "the depth" a well-defined function in the first place.

## Main results

* `Reaches p k` : the inductive predicate "`p` is obtained from the root seed `(2,1)` by `k`
  Berggren moves".
* `reaches_isSeed` : every reachable pair is a Euclid seed (soundness).
* `seed_reaches` : **completeness of the Berggren tree.** *Every* Euclid seed is reachable.
  The proof runs the explicit inverse move `parentSeed`, which is a genuine trichotomy in
  the slope: `n/m ∈ (1/2, 1)`, `(1/3, 1/2)`, `(0, 1/3)` selects `B₁`, `B₂`, `B₃`.
* `reaches_unique` : **the Berggren tree really is a tree.**  A seed is reachable at exactly
  one depth, so `depth` is a well-defined function on seeds.
* `reaches_fst_le` : a node at depth `k` has `m ≤ 2·3^k`; hence
  `reaches_log_hyp_le` : `log c ≤ log 8 + k · log 9`, and
  `dist_le_depth` / `depth_ge_dist` : `2 d(i, z) ≤ log 32 + k · log 9`, i.e.
  **the hyperbolic distance is, up to constants, a lower bound for the depth**.
  Combined with `depth_not_bounded_by_distance` of cycle I this is the exact truth:
  `d ≲ k`, and no reverse inequality holds.
* `mspine_dist_ge` : along the middle (Pell) spine the reverse inequality *does* hold,
  `k · log 2 ≤ d`, so on that branch depth and distance are commensurable.
* `berggren_depth_logarithmic_reach` : **the `O(log N)` statement of the mission, in the
  only form in which it is true.**  For every `N` there is a Berggren node of hypotenuse
  `≥ N` at depth `k = ⌊log₂ N⌋`, and `k · log 2 ≤ log N`.

Together: reaching size `N` costs depth `Θ(log N)` at best (`berggren_depth_logarithmic_reach`
for the upper bound, `depth_ge_dist` for the matching lower bound), while an arbitrary node of
hypotenuse `N` can sit at depth as large as `Θ(√N)` (cycle I).
-/

open HyperbolicBerggrenGeodesics

open Real

/-! ## Part A. Reachability in the Berggren tree -/




/-! ## Part B. The inverse move, and completeness of the tree -/











/-! ## Part C. Uniqueness of the depth -/




/-! ## Part D. Depth versus size: the lower bound -/






/-! ## Part E. Depth versus size: the matching upper bound along the Pell spine -/








/-! ## Part F. Depth is not governed by the continued fraction of the slope

The natural guess (conjecture **G1** of `FUTURE_DIRECTIONS.md`) is that a Berggren path is
the additive continued-fraction expansion of the slope `n/m`, so that the depth should equal
the sum of the partial quotients up to a bounded error, or at least up to a fixed
proportionality constant.  This is **false**, and the reason is structural: the move `B₃`
adds `2` to `m/n`, so a long run of `B₃`'s costs only *half* a partial quotient per step,
while the move `B₁` accumulates at the parabolic fixed point `n/m = 1` and costs a *whole*
partial quotient per step.  The two pure spines therefore realise two different
proportionality constants, and no single law can hold. -/


theorem cfSum_zero (n : ℕ) : cfSum n 0 = 0 := by rw [cfSum]

theorem cfSum_succ (n m : ℕ) :
    cfSum n (m + 1) = n / (m + 1) + cfSum (m + 1) (n % (m + 1)) := by rw [cfSum]

theorem cfSum_one_left (M : ℕ) : cfSum M 1 = M := by
  rw [cfSum_succ M 0, Nat.mod_one, cfSum_zero]
  simp

/-- `1/M = [0; M]`. -/
theorem cfSum_one (M : ℕ) (hM : 0 < M) : cfSum 1 M = M := by
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  rcases Nat.eq_zero_or_pos M' with rfl | hM'
  · simpa using cfSum_one_left 1
  · rw [cfSum_succ, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), cfSum_one_left]
    omega


/-- The **right spine**: `k` applications of `B₃` to the root give `(2k+2, 1)`, slope
`1/(2k+2)`, whose single partial quotient is `2k+2 = 2·depth + 2`. -/
theorem rspine_reaches (k : ℕ) : Reaches (2 * k + 2, 1) k := by
  induction k with
  | zero => exact Reaches.root
  | succ k ih =>
      have h : Reaches (seedR (2 * k + 2, 1)) (k + 1) := Reaches.stepR ih
      have he : seedR (2 * k + 2, 1) = (2 * (k + 1) + 2, 1) := by
        simp only [seedR, Prod.mk.injEq, and_true]
        omega
      rwa [he] at h

/-- The **left spine**: `k` applications of `B₁` to the root give `(k+2, k+1)`, slope
`(k+1)/(k+2)`, whose partial quotients sum to `k + 2 = depth + 2`. -/
theorem lspine_reaches (k : ℕ) : Reaches (k + 2, k + 1) k := by
  induction k with
  | zero => exact Reaches.root
  | succ k ih =>
      have h : Reaches (seedL (k + 2, k + 1)) (k + 1) := Reaches.stepL ih
      have he : seedL (k + 2, k + 1) = (k + 1 + 2, k + 1 + 1) := by
        simp only [seedL, Prod.mk.injEq, and_true]
        omega
      rwa [he] at h


/-! ## Part G. Non-vacuity witnesses -/





open HyperbolicBerggrenGeodesics in
theorem solution(lam C : ℝ) (hlam : 0 ≤ lam) :
    ¬ ∀ (m n k : ℕ), Reaches (m, n) k → |(k : ℝ) - lam * (cfSum n m : ℝ)| ≤ C := by
  intro H
  obtain ⟨k, hk⟩ := exists_nat_gt (3 * (C + 2 * lam))
  have h1 := H (2 * k + 2) 1 k (rspine_reaches k)
  have h2 := H (k + 2) (k + 1) k (lspine_reaches k)
  rw [cfSum_one _ (by omega)] at h1
  rw [cfSum_consec] at h2
  have h1' : |(k : ℝ) - lam * (2 * (k : ℝ) + 2)| ≤ C := by
    have : ((2 * k + 2 : ℕ) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
    rwa [this] at h1
  have h2' : |(k : ℝ) - lam * ((k : ℝ) + 2)| ≤ C := by
    have : ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 := by push_cast; ring
    rwa [this] at h2
  obtain ⟨hX1, hX2⟩ := abs_le.mp h1'
  obtain ⟨hY1, hY2⟩ := abs_le.mp h2'
  -- `2·(k − λ(k+2)) − (k − λ(2k+2)) = k − 2λ`, so `k ≤ 3C + 2λ`
  nlinarith [hk, hlam]
