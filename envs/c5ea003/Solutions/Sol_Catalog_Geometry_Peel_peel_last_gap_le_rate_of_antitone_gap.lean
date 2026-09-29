-- Prove2me | solution 1 for Catalog.Geometry.Peel.peel_last_gap_le_rate_of_antitone_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:35:50.928846+00:00
-- url     : https://prove2.me/submissions/3a6aa54f-d94a-4076-b43a-306e3899539e

-- Sol generated from Geometry/PeelStabilityConcentration.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Definitions.Def_Geometry_PeelSymmetryConstruction
import Theorems.Thm_Catalog_Geometry_Peel_nsmul_peelRate
import Theorems.Thm_Catalog_Geometry_Peel_sum_peelGap
/-
# Cycle 2: stability of the peeling bound, and boundary concentration

The first two files of this thread proved the peeling upper bound
(`exists_peel_stopping_time`, `peelEstimate_error`), its rigidity
(`peel_extremal_tfae`) and produced the matching `O(d)`-equivariant family of
equal-volume shell peelings of a Euclidean ball.  Rigidity is an all-or-nothing
statement: *exact* saturation forces the arithmetic profile.  This file closes
the two gaps that criticism of that statement immediately exposes.

1. **Stability.**  `peel_stability`: if every layer is at most `(1 + ε)` times
   the average rate — an approximate extremiser — then the profile is
   uniformly within `ε · budget` of the arithmetic one.  At `ε = 0` this
   recovers rigidity, and the bound is linear in `ε`, so approximate
   extremisers are approximately arithmetic.  The geometric consequence for
   ball peelings is `ball_peel_stability`.

2. **Maximal symmetry.**  `peel_extremal_iff_symmetric`: saturation of the
   pigeonhole bound is *equivalent* to invariance of the layer contents under
   the full symmetric group of the window.  Combined with
   `peel_extremal_of_cyclic_action` this shows that a single `N`-cycle already
   buys the whole symmetric group's worth of information.

3. **When no search is needed.**  `peel_last_gap_le_rate_of_antitone_gap`: for
   peelings with decreasing layer contents the last step of the window is
   always an admissible stopping time, and the first step is always
   inadmissible.  The existential in `exists_peel_stopping_time` is therefore
   only needed for genuinely oscillating peelings.

4. **Boundary concentration.**  `shell_thickness_le`: in the equal-volume
   shell peeling of `B(0,R) ⊆ ℝ^d`, the outermost shell carries a `1/N`
   fraction of the volume but has thickness at most `R / (d (N-1))`.  The
   discrepancy factor is exactly the dimension: equal-volume peelings of
   high-dimensional balls collapse onto the boundary sphere.  This is the
   quantitative reason ball peelings behave so differently from the abstract
   arithmetic profile they realise.

## Lab notes

`d = 10`, `N = 2`, `R = 1`: outer shell thickness `1 - 2^{-1/10} ≈ 0.0670`,
bound `1/(d(N-1)) = 0.1`; `d = 100`, `N = 2`: thickness `≈ 0.0069`, bound
`0.01`.  The bound is within roughly `30 %` of the truth in these ranges and
has the correct `1/d` decay, which is what the proof through the factorisation
`1 - s^d = (1-s)(1 + s + ... + s^{d-1})` is designed to capture.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric

variable (P : PeelProfile) {N k : ℕ}

/-! ## Stability of the peeling bound -/


/-! ## Maximal symmetry characterises the extremisers -/


/-! ## Monotone peelings need no search -/


/-! ## Boundary concentration of equal-volume shell peelings -/




/-! ## Stability for ball peelings -/



open Catalog.Geometry.Peel in
theorem solution(hN : 0 < N)
    (hmono : ∀ i j, i ≤ j → peelGap P j ≤ peelGap P i) :
    peelGap P (N - 1) ≤ peelRate P N ∧ peelRate P N ≤ peelGap P 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hbud : (N : ℝ) * peelRate P N = peelBudget P N := nsmul_peelRate P
  have hlow : (N : ℝ) * peelGap P (N - 1) ≤ peelBudget P N := by
    rw [← sum_peelGap P N]
    have : ∀ j ∈ range N, peelGap P (N - 1) ≤ peelGap P j := by
      intro j hj
      exact hmono j (N - 1) (by have := Finset.mem_range.1 hj; omega)
    have := Finset.card_nsmul_le_sum (range N) (fun j => peelGap P j) (peelGap P (N - 1)) this
    simpa [nsmul_eq_mul] using this
  have hhigh : peelBudget P N ≤ (N : ℝ) * peelGap P 0 := by
    rw [← sum_peelGap P N]
    have : ∀ j ∈ range N, peelGap P j ≤ peelGap P 0 := fun j _ => hmono 0 j (Nat.zero_le j)
    have := Finset.sum_le_card_nsmul (range N) (fun j => peelGap P j) (peelGap P 0) this
    simpa [nsmul_eq_mul] using this
  constructor
  · nlinarith
  · nlinarith
