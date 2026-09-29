-- Prove2me | solution 1 for FactoringLab.structural_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:16:21.549788+00:00
-- url     : https://prove2.me/submissions/e9372faa-bf15-468c-bc79-9a3bb5a2d38d

-- Sol generated from Probability/StructuralOrthogonality.lean
import Mathlib
import Definitions.Def_Probability_StructuralOrthogonality
import Theorems.Thm_FactoringLab_sum_residual_band
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









/-- Summing a function over `Ω` can be done band by band. -/
theorem sum_by_band (Ω : Finset ι) (n : ι → κ) (F : ι → ℝ) :
    ∑ k ∈ Ω.image n, ∑ i ∈ Ω.filter (fun i => n i = k), F i = ∑ i ∈ Ω, F i :=
  Finset.sum_fiberwise_of_maps_to (fun _ hi => Finset.mem_image_of_mem n hi) F









/-! ### Quantitative form: no `N`-only invariant predicts better than the band mean -/






/-! ### Quantitative near-equal-`N` test: Cauchy–Schwarz against the band spread -/




/-! ### Free-witness aggregation -/





open FactoringLab in
theorem solution(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
    ∑ i ∈ Ω, g (n i) * (Y i - bandMean Ω n Y i) = 0 := by
  rw [← sum_by_band Ω n (fun i => g (n i) * (Y i - bandMean Ω n Y i))]
  refine Finset.sum_eq_zero fun k hk => ?_
  have : ∑ i ∈ Ω.filter (fun i => n i = k), g (n i) * (Y i - bandMean Ω n Y i)
      = g k * ∑ i ∈ Ω.filter (fun i => n i = k), (Y i - bandMean Ω n Y i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.1 hi).2]
  rw [this, sum_residual_band Ω n Y hk, mul_zero]
