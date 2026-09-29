-- Prove2me | Theorems.Thm_FactoringLab_nearEqualN_test
-- name    : FactoringLab.nearEqualN_test
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:31:46.004333+00:00
-- url     : https://prove2.me/theorems/6eb1a66e-6956-4a47-9d41-2567a4ea782a
-- title:
--   The near-equal-`N` test, formalized.
-- statement:
--   **The near-equal-`N` test, formalized.**  If the band means of the target
--   are constant across the population — the situation engineered by grouping
--   semiprimes into a narrow size band — then *every* invariant computable from the
--   band label alone has exactly zero covariance with the target.
--
--   ```lean
--   theorem FactoringLab.nearEqualN_test(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (c : ℝ)
--       (hconst : ∀ i ∈ Ω, bandMean Ω n Y i = c) (g : κ → ℝ) :
--       cov Ω (fun i => g (n i)) Y = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/StructuralOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/StructuralOrthogonality.lean#L134

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

theorem FactoringLab.nearEqualN_test(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (c : ℝ)
    (hconst : ∀ i ∈ Ω, bandMean Ω n Y i = c) (g : κ → ℝ) :
    cov Ω (fun i => g (n i)) Y = 0 := by sorry
