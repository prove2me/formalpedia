-- Prove2me | solution 1 for FactoringLab.cov_sq_le_variance_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:15:22.318187+00:00
-- url     : https://prove2.me/submissions/b8cae407-b6a2-4df0-aa81-8e40f1d69adf

-- Sol generated from Probability/StructuralOrthogonality.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_cov_centered
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
    (cov Ω X Y) ^ 2 ≤ variance Ω X * variance Ω Y := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Ω
    (fun i => X i - FactoringLab.expect Ω X) (fun i => Y i - FactoringLab.expect Ω Y)
  have hc : (0 : ℝ) ≤ (Ω.card : ℝ) ^ 2 := sq_nonneg _
  rw [cov_centered Ω X Y, div_pow]
  have hvx : variance Ω X = (∑ i ∈ Ω, (X i - FactoringLab.expect Ω X) ^ 2) / Ω.card := by
    rw [variance, cov_centered Ω X X]
    exact congrArg (· / (Ω.card : ℝ)) (Finset.sum_congr rfl fun i _ => by ring)
  have hvy : variance Ω Y = (∑ i ∈ Ω, (Y i - FactoringLab.expect Ω Y) ^ 2) / Ω.card := by
    rw [variance, cov_centered Ω Y Y]
    exact congrArg (· / (Ω.card : ℝ)) (Finset.sum_congr rfl fun i _ => by ring)
  rw [hvx, hvy, div_mul_div_comm, ← sq]
  rcases Finset.eq_empty_or_nonempty Ω with rfl | hΩ
  · simp
  · have hcard : (0 : ℝ) < (Ω.card : ℝ) := by exact_mod_cast hΩ.card_pos
    gcongr
