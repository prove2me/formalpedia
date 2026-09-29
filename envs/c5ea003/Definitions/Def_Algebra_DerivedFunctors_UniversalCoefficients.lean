-- Prove2me | Definitions.Def_Algebra_DerivedFunctors_UniversalCoefficients
-- name    : Algebra_DerivedFunctors_UniversalCoefficients
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:13:42.429088+00:00
-- url     : https://prove2.me/theorems/14863cf3-8c9e-4db1-ac40-15dfc7d2e451
-- title:
--   Aether Catalog definitions — Algebra_DerivedFunctors_UniversalCoefficients
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.DerivedFunctors.UniversalCoefficients`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/DerivedFunctors/UniversalCoefficients.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.DerivedFunctors

section Flat

variable {R : Type u} [CommRing R] (G : ModuleCat.{u} R) [Module.Flat R G]
  {ι : Type v} {c : ComplexShape ι}

/-- **Universal coefficient theorem, flat coefficients.**
For a flat module `G` the homology of `G ⊗ C` is `G ⊗ H(C)`. -/
noncomputable def homologyTensorFlatIso (K : HomologicalComplex (ModuleCat.{u} R) c) (n : ι) :
    (((tensorLeft G).mapHomologicalComplex c).obj K).homology n ≅
      (tensorLeft G).obj (K.homology n) :=
  (K.sc n).mapHomologyIso (tensorLeft G)



end Flat

section NotFlat

/-- Multiplication by `k` on `ℤ`, as a short complex `0 → ℤ → ℤ`. -/
noncomputable def mulShortComplex (k : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (0 : ModuleCat.of ℤ PUnit ⟶ ModuleCat.of ℤ ℤ)
    (ModuleCat.ofHom ((k : ℤ) • LinearMap.id)) (by simp)



end NotFlat

end Catalog.DerivedFunctors


