-- Prove2me | Definitions.Def_Probability_StructuralOrthogonality
-- name    : Probability_StructuralOrthogonality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:26.154359+00:00
-- url     : https://prove2.me/theorems/174b07cd-e902-4d91-bcdb-06eaaed9c200
-- title:
--   Aether Catalog definitions — Probability_StructuralOrthogonality
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.StructuralOrthogonality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/StructuralOrthogonality.lean by skeleton subtraction
import Mathlib
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

namespace FactoringLab

open Finset

variable {ι κ : Type*} [DecidableEq κ]

/-- The fiber (`band`) of the population `Ω` containing `i`, i.e. all members
of the population sharing the band label of `i`. -/
def band (Ω : Finset ι) (n : ι → κ) (i : ι) : Finset ι :=
  Ω.filter (fun j => n j = n i)

/-- The conditional expectation `E[Y | n]` on a finite uniform population:
the average of `Y` over the band of `i`. -/
noncomputable def bandMean (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ band Ω n i, Y j) / (band Ω n i).card

/-- Uniform expectation over the finite population `Ω`. -/
noncomputable def expect (Ω : Finset ι) (Y : ι → ℝ) : ℝ :=
  (∑ i ∈ Ω, Y i) / Ω.card

/-- Covariance of two random variables under the uniform law on `Ω`. -/
noncomputable def cov (Ω : Finset ι) (X Y : ι → ℝ) : ℝ :=
  expect Ω (fun i => X i * Y i) - expect Ω X * expect Ω Y

/-- Variance under the uniform law on `Ω`. -/
noncomputable def variance (Ω : Finset ι) (X : ι → ℝ) : ℝ := cov Ω X X

/-- Pearson correlation under the uniform law on `Ω`. -/
noncomputable def corr (Ω : Finset ι) (X Y : ι → ℝ) : ℝ :=
  cov Ω X Y / (Real.sqrt (variance Ω X) * Real.sqrt (variance Ω Y))

section Fibers




end Fibers







/-! ### Quantitative form: no `N`-only invariant predicts better than the band mean -/

/-- The band mean as a genuine function of the band label alone. -/
noncomputable def bandMeanFn (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (k : κ) : ℝ :=
  (∑ j ∈ Ω.filter (fun j => n j = k), Y j) / (Ω.filter (fun j => n j = k)).card





/-! ### Quantitative near-equal-`N` test: Cauchy–Schwarz against the band spread -/




/-! ### Free-witness aggregation -/




end FactoringLab


