-- Prove2me | solution 1 for Catalog.Geometry.Peel.ball_peel_stability
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:15:27.188274+00:00
-- url     : https://prove2.me/submissions/7b1db722-340e-4352-b590-2bed4ddfa1dc

-- Sol generated from Geometry/PeelStabilityConcentration.lean
import Mathlib
import Definitions.Def_Geometry_PeelStoppingTime
import Definitions.Def_Geometry_PeelSymmetryConstruction
import Theorems.Thm_Catalog_Geometry_Peel_ballVol_zero
import Theorems.Thm_Catalog_Geometry_Peel_peel_stability
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
theorem solution(d N : ℕ) (hd : 0 < d) (hN : 0 < N) {R : ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) (r : ℕ → ℝ) (hanti : Antitone r) (hnn : ∀ k, 0 ≤ r k)
    (h0 : r 0 = R) (hlast : r N = 0)
    (hsmall : ∀ j < N, ballVol d (r j) - ballVol d (r (j + 1)) ≤ (1 + ε) * (ballVol d R / N))
    (hk : k ≤ N) :
    |ballVol d (r k) - ballVol d R * (1 - (k : ℝ) / N)| ≤ ε * ballVol d R := by
  set P := radiusProfile d hd r hanti hnn with hP
  have hsize : ∀ j, P.size j = ballVol d (r j) := fun _ => rfl
  have hbudget : peelBudget P N = ballVol d R := by simp [peelBudget, hsize, h0, hlast]
  have hrate : peelRate P N = ballVol d R / N := by rw [peelRate, hbudget]
  have hgap : ∀ j < N, peelGap P j ≤ (1 + ε) * peelRate P N := by
    intro j hj
    rw [hrate, peelGap, hsize, hsize]
    exact hsmall j hj
  have hstab := peel_stability P hε hk hgap
  rw [hbudget] at hstab
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hest : peelEstimate P N k = ballVol d R * (1 - (k : ℝ) / N) := by
    rw [peelEstimate, hsize, h0, hrate]
    field_simp
  rw [hest, hsize] at hstab
  exact hstab
