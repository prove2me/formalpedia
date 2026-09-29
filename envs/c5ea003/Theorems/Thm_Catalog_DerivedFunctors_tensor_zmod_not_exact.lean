-- Prove2me | Theorems.Thm_Catalog_DerivedFunctors_tensor_zmod_not_exact
-- name    : Catalog.DerivedFunctors.tensor_zmod_not_exact
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:56.839602+00:00
-- url     : https://prove2.me/theorems/ccc348a5-4c49-4edb-8e35-00249bbd005a
-- title:
--   The correction term in the universal coefficient theorem is genuinely needed.
-- statement:
--   **The correction term in the universal coefficient theorem is genuinely needed.**
--   Although `0 → ℤ --(·k)--> ℤ` is exact, tensoring with the (non-flat) coefficient module `ZMod k`
--   destroys exactness for `k ≥ 2`: the class of `1 ⊗ 1` is a nonzero cycle which is not a boundary.
--   This surviving class is the `Tor₁`-term of the universal coefficient sequence.
--
--   ```lean
--   theorem Catalog.DerivedFunctors.tensor_zmod_not_exact(k : ℕ) (hk : 2 ≤ k) :
--       ¬ ((mulShortComplex k).map (tensorLeft (ModuleCat.of ℤ (ZMod k)))).Exact := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/DerivedFunctors/UniversalCoefficients.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/DerivedFunctors/UniversalCoefficients.lean#L85

-- Thm stub generated from Algebra/DerivedFunctors/UniversalCoefficients.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_UniversalCoefficients

/-!
# Universal coefficients: flat coefficients and the failure of flatness

The universal coefficient theorem for homology relates `H_n(C ⊗ G)` with `H_n(C) ⊗ G` and a
correction term `Tor₁(H_{n-1}(C), G)`. This file formalises the two extreme phenomena:

* `Catalog.DerivedFunctors.homologyTensorFlatIso`: **the universal coefficient theorem with flat
  coefficients**. If `G` is a flat `R`-module, the correction term disappears and
  `H_n(C ⊗ G) ≅ H_n(C) ⊗ G` for every complex `C` of `R`-modules (any complex shape).
  A `LinearEquiv` version is `Catalog.DerivedFunctors.homologyTensorFlatLinearEquiv`, and
  `Catalog.DerivedFunctors.homology_tensor_eq_zero_of_flat` records that tensoring with a flat
  module preserves acyclicity.

* `Catalog.DerivedFunctors.tensor_zmod_not_exact`: for non-flat coefficients the correction term is
  really needed. The short complex `0 → ℤ --(·k)--> ℤ` of `ℤ`-modules is exact (multiplication by
  `k ≠ 0` is injective, i.e. `H₁` of the two-term complex vanishes), yet after tensoring with
  `ZMod k` (`k ≥ 2`) it is no longer exact: a nonzero class survives, which is exactly the
  `Tor₁(ZMod k, ZMod k)`-term of the universal coefficient sequence.
-/

universe u v

open CategoryTheory MonoidalCategory Limits HomologicalComplex
open scoped TensorProduct

open Catalog.DerivedFunctors


variable {R : Type u} [CommRing R] (G : ModuleCat.{u} R) [Module.Flat R G]
  {ι : Type v} {c : ComplexShape ι}

theorem Catalog.DerivedFunctors.tensor_zmod_not_exact(k : ℕ) (hk : 2 ≤ k) :
    ¬ ((mulShortComplex k).map (tensorLeft (ModuleCat.of ℤ (ZMod k)))).Exact := by sorry
