-- Prove2me | Theorems.Thm_FactoringLab_cov_eq_cov_bandMean
-- name    : FactoringLab.cov_eq_cov_bandMean
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:47.426733+00:00
-- url     : https://prove2.me/theorems/685a0b4c-5023-41f2-b431-f3fe71488214
-- title:
--   All correlation is band correlation.
-- statement:
--   **All correlation is band correlation.**  For any invariant computable from
--   the band label alone, its covariance with the target equals its covariance with
--   the band means of the target.
--
--   ```lean
--   theorem FactoringLab.cov_eq_cov_bandMean(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
--       cov Ω (fun i => g (n i)) Y = cov Ω (fun i => g (n i)) (bandMean Ω n Y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/StructuralOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/StructuralOrthogonality.lean#L117

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

theorem FactoringLab.cov_eq_cov_bandMean(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
    cov Ω (fun i => g (n i)) Y = cov Ω (fun i => g (n i)) (bandMean Ω n Y) := by sorry
