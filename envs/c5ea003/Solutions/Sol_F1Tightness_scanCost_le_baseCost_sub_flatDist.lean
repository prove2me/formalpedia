-- Prove2me | solution 1 for F1Tightness.scanCost_le_baseCost_sub_flatDist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:01:43.204995+00:00
-- url     : https://prove2.me/submissions/f829bea4-19e8-4a0d-86c1-8f17a684e324

-- Sol generated from Probability/F1TightnessQuantitative.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessQuantitative
import Theorems.Thm_F1Tightness_abs_sub_le_pair
import Theorems.Thm_F1Tightness_row_sum_ge
import Theorems.Thm_F1Tightness_sum_pairs_identity
import Theorems.Thm_F1Tightness_sum_rank_weights

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
theorem solution{p : Fin M → ℝ}
    (hsum : ∑ i : Fin M, p i = 1) (hanti : Antitone p) :
    scanCost p ≤ baseCost M - flatDist p / 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by norm_num)
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set a : Fin M → ℝ := fun i => ((i : ℕ) : ℝ) + 1 with ha
  -- the pairwise identity, with the quadratic remainder kept
  have hid : ∑ i : Fin M, ∑ j : Fin M, (a i - a j) * (p i - p j)
      = 2 * ((M : ℝ) * scanCost p - (M : ℝ) * ((M : ℝ) + 1) / 2) := by
    have := sum_pairs_identity (univ : Finset (Fin M)) a p
    rw [Finset.card_univ, Fintype.card_fin, sum_rank_weights, hsum] at this
    simpa [scanCost, ha, mul_comm, mul_left_comm, mul_assoc] using this
  -- each pairwise term dominates the absolute difference
  have hterm : ∀ i j : Fin M, |p i - p j| ≤ -((a i - a j) * (p i - p j)) := by
    intro i j
    have h := abs_sub_le_pair hanti i j
    have : (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) * (p i - p j) = -((a i - a j) * (p i - p j)) := by
      simp only [ha]; ring
    linarith [h, this.le, this.ge]
  have hdouble : ∑ i : Fin M, ∑ j : Fin M, |p i - p j|
      ≤ ∑ i : Fin M, ∑ j : Fin M, -((a i - a j) * (p i - p j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  have hneg : ∑ i : Fin M, ∑ j : Fin M, -((a i - a j) * (p i - p j))
      = -(∑ i : Fin M, ∑ j : Fin M, (a i - a j) * (p i - p j)) := by
    simp [Finset.sum_neg_distrib]
  -- the L¹ lower bound on the double sum
  have hrow : (M : ℝ) * flatDist p ≤ ∑ i : Fin M, ∑ j : Fin M, |p i - p j| := by
    rw [flatDist, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => row_sum_ge hsum i
  rw [hneg, hid] at hdouble
  have hkey : (M : ℝ) * flatDist p
      ≤ -(2 * ((M : ℝ) * scanCost p - (M : ℝ) * ((M : ℝ) + 1) / 2)) := le_trans hrow hdouble
  have hb : baseCost M = ((M : ℝ) + 1) / 2 := rfl
  rw [hb]
  nlinarith [hkey]
