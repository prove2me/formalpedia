-- Prove2me | solution 1 for FactoringLab.sum_residual_band
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:35:42.721722+00:00
-- url     : https://prove2.me/submissions/c63c471e-74c9-4c9e-9cba-887f926f5524

-- Sol generated from Probability/StructuralOrthogonality.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
/-
# Structural Orthogonality (Factoring Lab, Phase A v19c)

The *core* pattern of the eight-barrier framework, stated and proved as a
theorem of elementary probability on a finite sample space.

Setting.  A finite population `Ω` of semiprimes (or of any objects), each
carrying a *band label* `n i` (in the lab: the size band `N / 40`, or simply
`N` itself), and a *target* `Y i` (in the lab: the smaller prime factor `p`).
An *invariant computable from `N` alone* is exactly a random variable of the
form `g ∘ n`.

Main results.

* `FactoringLab.structural_orthogonality`: every invariant `g ∘ n` computable
  from the band label alone is orthogonal to the *residual* `Y - E[Y | n]`.
  This is the exact sense in which "any computable function of `N` alone is
  `N`-only": it carries no information about `Y` beyond the band mean.
* `FactoringLab.cov_eq_cov_bandMean`: consequently the covariance of any such
  invariant with `Y` equals its covariance with the band means, i.e. *all*
  observed correlation is explained by the band.
* `FactoringLab.nearEqualN_test`: the formal near-equal-`N` test.  If the band
  means of `Y` are constant across the population, then **every** invariant
  computable from `n` alone has exactly zero covariance with `Y`.
* `FactoringLab.corr_zero_of_bandMean_const`: the same conclusion for the
  Pearson correlation coefficient.
-/

open FactoringLab

open Finset

variable {ι κ : Type*} [DecidableEq κ]








/-- Members of the same band have the same band mean. -/
theorem bandMean_congr (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) {i j : ι}
    (h : n j = n i) : bandMean Ω n Y j = bandMean Ω n Y i := by
  unfold bandMean band
  simp [h]










/-! ### Quantitative form: no `N`-only invariant predicts better than the band mean -/






/-! ### Quantitative near-equal-`N` test: Cauchy–Schwarz against the band spread -/




/-! ### Free-witness aggregation -/





open FactoringLab in
theorem solution(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) {k : κ}
    (hk : k ∈ Ω.image n) :
    ∑ i ∈ Ω.filter (fun i => n i = k), (Y i - bandMean Ω n Y i) = 0 := by
  obtain ⟨i₀, hi₀Ω, hi₀⟩ := Finset.mem_image.1 hk
  have hfib : Ω.filter (fun i => n i = k) = band Ω n i₀ := by
    unfold band; rw [hi₀]
  have hne : (band Ω n i₀).Nonempty := ⟨i₀, by simp [band, hi₀Ω]⟩
  have hcard : ((band Ω n i₀).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
  rw [hfib, Finset.sum_sub_distrib]
  have hconst : ∀ i ∈ band Ω n i₀, bandMean Ω n Y i = bandMean Ω n Y i₀ := by
    intro i hi
    exact bandMean_congr Ω n Y (by simpa [band] using (Finset.mem_filter.1 hi).2)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  unfold bandMean
  field_simp
  ring
