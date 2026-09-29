-- Prove2me | solution 1 for Catalog.Geometry.Peel.shell_thickness_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:35:52.432619+00:00
-- url     : https://prove2.me/submissions/5f9b53a1-11a4-437a-9871-a9ba982ac542

-- Sol generated from Geometry/PeelStabilityConcentration.lean
import Mathlib
import Definitions.Def_Geometry_PeelSymmetryConstruction
import Theorems.Thm_Catalog_Geometry_Peel_one_sub_rpow_inv_le
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
theorem solution(d N : ℕ) (hd : 0 < d) (hN : 2 ≤ N) {R : ℝ} (hR : 0 ≤ R) :
    R - shellRadius R d N 1 ≤ R / (d * ((N : ℝ) - 1)) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hrad : shellRadius R d N 1 = R * (1 - 1 / (N : ℝ)) ^ ((d : ℝ)⁻¹) := by
    have hmax : max (0 : ℝ) (1 - ((1 : ℕ) : ℝ) / (N : ℝ)) = 1 - 1 / (N : ℝ) := by
      rw [Nat.cast_one]
      refine max_eq_right ?_
      rw [sub_nonneg, div_le_one hNpos]
      linarith
    rw [shellRadius, hmax]
  have hbase := one_sub_rpow_inv_le d N hd hN
  rw [hrad]
  have : R - R * (1 - 1 / (N : ℝ)) ^ ((d : ℝ)⁻¹)
      = R * (1 - (1 - 1 / (N : ℝ)) ^ ((d : ℝ)⁻¹)) := by ring
  rw [this]
  calc R * (1 - (1 - 1 / (N : ℝ)) ^ ((d : ℝ)⁻¹))
      ≤ R * (1 / (d * ((N : ℝ) - 1))) := by
        exact mul_le_mul_of_nonneg_left hbase hR
    _ = R / (d * ((N : ℝ) - 1)) := by ring
