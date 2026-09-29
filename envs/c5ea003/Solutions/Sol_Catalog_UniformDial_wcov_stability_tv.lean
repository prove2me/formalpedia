-- Prove2me | solution 1 for Catalog.UniformDial.wcov_stability_tv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:28.094632+00:00
-- url     : https://prove2.me/submissions/e1582396-3921-4786-8f8a-8bcb024afc69

-- Sol generated from Combinatorics/UniformDialDrawInvariance.lean
import Mathlib
import Definitions.Def_Combinatorics_UniformDialDrawInvariance
import Theorems.Thm_Catalog_UniformDial_pair_mass_l1
import Theorems.Thm_Catalog_UniformDial_wcov_eq_half_double_sum
/-
# The yield dial is draw-regime invariant

Setting.  A finite population `ι` of "keys".  Each key `i` carries a *footprint* `x i`
(the weight used by the dial) and a *yield rate* `y i`.  A **draw regime** is a
probability weighting `p : ι → ℝ` (`p ≥ 0`, `∑ p = 1`): uniform draws, balanced draws
and genuinely unbalanced draws are all instances of the same object.

The experimental claim under test (`DIAL-IS-DRAW-INVARIANT`) is that the association
between the footprint dial and the yield rate does **not** get diluted when the draw
regime is changed.  This file isolates the exact structural reason, and quantifies the
residual regime dependence:

* `wcov_eq_half_double_sum` — the Hoeffding/Chebyshev pair identity: the weighted
  covariance is a *pairwise* functional of the population.
* `wcov_nonneg_of_comonotone` — if the population is comonotone (no discordant pair),
  the dial has nonnegative covariance with the rate **in every draw regime**.
* `wcov_pos_of_comonotone` — strict positivity survives as soon as one strictly ordered
  pair is charged by the regime; hence full-support regimes cannot dilute the signal.
* `dial_sign_draw_invariant` — the two-regime form of the claim (uniform vs unbalanced).
* `wcov_monotone_comp_nonneg` — the same holds after arbitrary monotone re-encodings of
  footprint and rate, i.e. for rank (Spearman-type) versions of the dial.
* `wcov_stability_tv` — a quantitative bound: changing the draw regime moves the dial's
  covariance by at most `(range x) * (range y)` times the ℓ¹ (twice total variation)
  distance between the regimes.  "Identical within noise" is therefore forced whenever
  the two regimes are ℓ¹-close, and cannot be worse than this bound in general.

All statements are for an arbitrary finite index type; nothing here is specific to a
sampling seed.
-/

open Finset

open Catalog.UniformDial

variable {ι : Type*} [Fintype ι]















variable {p q x y : ι → ℝ} {Mx My : ℝ}

omit [Fintype ι] in
private lemma range_nonneg (hx : ∀ i j, |x i - x j| ≤ Mx) [Nonempty ι] : 0 ≤ Mx := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := hx i i
  simpa using this





open Catalog.UniformDial in
theorem solution(hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∑ i, p i = 1) (hq : ∑ i, q i = 1)
    (hx : ∀ i j, |x i - x j| ≤ Mx) (hy : ∀ i j, |y i - y j| ≤ My) :
    |wcov p x y - wcov q x y| ≤ Mx * My * ∑ i, |p i - q i| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [wcov, wmean, Finset.sum_empty, Finset.univ_eq_empty]
  have hMx : 0 ≤ Mx := range_nonneg hx
  have hMy : 0 ≤ My := range_nonneg hy
  have hdiff : (2 : ℝ) * (wcov p x y - wcov q x y)
      = ∑ i, ∑ j, (p i * p j - q i * q j) * ((x i - x j) * (y i - y j)) := by
    have h1 := wcov_eq_half_double_sum (p := p) (x := x) (y := y) hp
    have h2 := wcov_eq_half_double_sum (p := q) (x := x) (y := y) hq
    have : ∑ i, ∑ j, (p i * p j - q i * q j) * ((x i - x j) * (y i - y j))
        = (∑ i, ∑ j, p i * p j * ((x i - x j) * (y i - y j)))
          - ∑ i, ∑ j, q i * q j * ((x i - x j) * (y i - y j)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, ← h1, ← h2]; ring
  have habs : |(2 : ℝ) * (wcov p x y - wcov q x y)|
      ≤ Mx * My * ∑ i, ∑ j, |p i * p j - q i * q j| := by
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_mul]
    have h1 : |x i - x j| * |y i - y j| ≤ Mx * My :=
      mul_le_mul (hx i j) (hy i j) (abs_nonneg _) hMx
    calc |p i * p j - q i * q j| * (|x i - x j| * |y i - y j|)
        ≤ |p i * p j - q i * q j| * (Mx * My) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = Mx * My * |p i * p j - q i * q j| := by ring
  have hl1 := pair_mass_l1 hp0 hq0 hp hq
  have hMM : 0 ≤ Mx * My := mul_nonneg hMx hMy
  have : |(2 : ℝ) * (wcov p x y - wcov q x y)| ≤ Mx * My * (2 * ∑ i, |p i - q i|) :=
    habs.trans (mul_le_mul_of_nonneg_left hl1 hMM)
  rw [abs_mul] at this
  simp only [abs_two] at this
  linarith
