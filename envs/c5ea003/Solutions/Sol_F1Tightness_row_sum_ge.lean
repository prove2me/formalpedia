-- Prove2me | solution 1 for F1Tightness.row_sum_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:04.511276+00:00
-- url     : https://prove2.me/submissions/6e09e9eb-37bc-43b7-876f-eefa3e072d2f

-- Sol generated from Probability/F1TightnessQuantitative.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative

/-!
# A quantitative (L¹) strengthening of the F1 master inequality

`Probability.F1TightnessCore` proves that on an antitone non-flat profile the
slack factor `X = C₀/c_asc` is strictly larger than one, so the master bound is
never attained; but `one_lt_gapX` is qualitative — it gives no number.

This file supplies the number.  Write

`flatDist p = ∑ i, |p i − 1/M|`

for the L¹ distance of the profile to the flat profile.  Then, for every
antitone profile,

* `scanCost_le_baseCost_sub_flatDist` — `c_asc ≤ C₀ − ‖p − flat‖₁ / 2`;
* `one_add_flatDist_le_gapX` — `1 + ‖p − flat‖₁/(2M) ≤ X`;
* `speedup_mul_le_bound_quantitative` — **the refined master inequality**
  `S · (1 + ‖p − flat‖₁/(2M)) ≤ bound`, i.e. `S ≤ bound/(1 + V)` with the
  explicit, computable dispersion functional `V = ‖p − flat‖₁/(2M)`;
* `flatDist_eq_zero_iff` — `V` vanishes exactly on the flat profile, the case
  the three independent tests reject pool-side.

The proof route is the pairwise expansion `sum_pairs_identity` of the core file,
kept with its quadratic remainder instead of discarded: for an antitone profile
each pairwise term of the Chebyshev double sum is bounded below by `|p i − p j|`
in absolute value, and the triangle inequality converts the resulting double sum
into the L¹ distance to flat.  This is the shape asked for by direction 3 of
`FUTURE_DIRECTIONS.md`, with the absolute constant `c = 1` in the normalisation
`V = ‖p − flat‖₁/(2M)`.
-/

open F1Tightness

open Finset

variable {M : ℕ}











/-! ## Non-vacuity: an explicit profile with a positive dispersion -/








open F1Tightness in
theorem solution{p : Fin M → ℝ} (hsum : ∑ i : Fin M, p i = 1) (i : Fin M) :
    (M : ℝ) * |p i - (M : ℝ)⁻¹| ≤ ∑ j : Fin M, |p i - p j| := by
  have htri : |∑ j : Fin M, (p i - p j)| ≤ ∑ j : Fin M, |p i - p j| :=
    Finset.abs_sum_le_sum_abs _ _
  have hrow : ∑ j : Fin M, (p i - p j) = (M : ℝ) * p i - 1 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [nsmul_eq_mul]
  rw [hrow] at htri
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hfac : (M : ℝ) * |p i - (M : ℝ)⁻¹| = |(M : ℝ) * p i - 1| := by
      rw [← abs_of_pos hMR, ← abs_mul, abs_of_pos hMR]
      congr 1
      field_simp
    rw [hfac]
    exact htri
