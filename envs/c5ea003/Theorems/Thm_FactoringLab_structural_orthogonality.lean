-- Prove2me | Theorems.Thm_FactoringLab_structural_orthogonality
-- name    : FactoringLab.structural_orthogonality
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:53.363136+00:00
-- url     : https://prove2.me/theorems/a3d147b8-63ff-4dd1-96cd-a2ac935efb27
-- title:
--   Structural orthogonality.
-- statement:
--   **Structural orthogonality.**  Every invariant `g ∘ n` that is computable
--   from the band label alone (in the lab: from `N` alone) is orthogonal to the
--   residual `Y - E[Y | n]` of the target.  No such invariant carries any linear
--   information about `Y` beyond what the band label already determines.
--
--   ```lean
--   theorem FactoringLab.structural_orthogonality(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
--       ∑ i ∈ Ω, g (n i) * (Y i - bandMean Ω n Y i) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/StructuralOrthogonality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/StructuralOrthogonality.lean#L93

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

theorem FactoringLab.structural_orthogonality(Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ) (g : κ → ℝ) :
    ∑ i ∈ Ω, g (n i) * (Y i - bandMean Ω n Y i) = 0 := by sorry
