-- Prove2me | Theorems.Thm_FactoringLab_cov_sq_le_variance_mul
-- name    : FactoringLab.cov_sq_le_variance_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:29:01.402056+00:00
-- url     : https://prove2.me/theorems/88d40a12-81d5-4d51-9a3e-aaffcb5c8874
-- title:
--   Cauchy–Schwarz for the empirical covariance.
-- statement:
--   **Cauchy–Schwarz for the empirical covariance.**
--
--   ```lean
--   theorem FactoringLab.cov_sq_le_variance_mul(Ω : Finset ι) (X Y : ι → ℝ) :
--       (cov Ω X Y) ^ 2 ≤ variance Ω X * variance Ω Y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/StructuralOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/StructuralOrthogonality.lean#L230

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


















/-! ### Quantitative form: no `N`-only invariant predicts better than the band mean -/






/-! ### Quantitative near-equal-`N` test: Cauchy–Schwarz against the band spread -/

theorem FactoringLab.cov_sq_le_variance_mul(Ω : Finset ι) (X Y : ι → ℝ) :
    (cov Ω X Y) ^ 2 ≤ variance Ω X * variance Ω Y := by sorry
