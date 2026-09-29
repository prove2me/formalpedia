-- Prove2me | solution 1 for FactoringLab.cov_centered
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:12:04.608731+00:00
-- url     : https://prove2.me/submissions/e3f4512b-ad1e-4c98-8e85-50ea3f4f0c94

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


















/-! ### Quantitative form: no `N`-only invariant predicts better than the band mean -/






/-! ### Quantitative near-equal-`N` test: Cauchy–Schwarz against the band spread -/




/-! ### Free-witness aggregation -/





open FactoringLab in
theorem solution(Ω : Finset ι) (X Y : ι → ℝ) :
    FactoringLab.cov Ω X Y
      = (∑ i ∈ Ω, (X i - FactoringLab.expect Ω X) * (Y i - FactoringLab.expect Ω Y)) / Ω.card := by
  rcases Finset.eq_empty_or_nonempty Ω with rfl | hΩ
  · simp [FactoringLab.cov, FactoringLab.expect]
  · have hcard : (Ω.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hΩ.card_pos.ne'
    have hexp : ∀ i ∈ Ω, (X i - FactoringLab.expect Ω X) * (Y i - FactoringLab.expect Ω Y)
        = X i * Y i - FactoringLab.expect Ω X * Y i - FactoringLab.expect Ω Y * X i
          + FactoringLab.expect Ω X * FactoringLab.expect Ω Y := fun i _ => by ring
    rw [Finset.sum_congr rfl hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    unfold FactoringLab.cov FactoringLab.expect
    field_simp
    ring
