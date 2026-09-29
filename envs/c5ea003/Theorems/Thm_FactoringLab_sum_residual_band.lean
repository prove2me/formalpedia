-- Prove2me | Theorems.Thm_FactoringLab_sum_residual_band
-- name    : FactoringLab.sum_residual_band
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:40.545124+00:00
-- url     : https://prove2.me/theorems/de677e11-8c8f-4284-95b5-1290af4b8767
-- title:
--   On a single band, the residual `Y - E[Y | n]` sums to zero.
-- statement:
--   On a single band, the residual `Y - E[Y | n]` sums to zero.
--
--   ```lean
--   theorem FactoringLab.sum_residual_band(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) {k : κ}
--       (hk : k ∈ Ω.image n) :
--       ∑ i ∈ Ω.filter (fun i => n i = k), (Y i - bandMean Ω n Y i) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/StructuralOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/StructuralOrthogonality.lean#L73

-- Thm stub generated from Probability/StructuralOrthogonality.lean
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

theorem FactoringLab.sum_residual_band(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) {k : κ}
    (hk : k ∈ Ω.image n) :
    ∑ i ∈ Ω.filter (fun i => n i = k), (Y i - bandMean Ω n Y i) = 0 := by sorry
