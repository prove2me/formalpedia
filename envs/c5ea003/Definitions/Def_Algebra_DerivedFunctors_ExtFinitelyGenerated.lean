-- Prove2me | Definitions.Def_Algebra_DerivedFunctors_ExtFinitelyGenerated
-- name    : Algebra_DerivedFunctors_ExtFinitelyGenerated
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:12.168846+00:00
-- url     : https://prove2.me/theorems/ef4afaa1-c7bd-4175-ada7-10c2b6a00b7d
-- title:
--   Aether Catalog definitions — Algebra_DerivedFunctors_ExtFinitelyGenerated
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.DerivedFunctors.ExtFinitelyGenerated`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/DerivedFunctors/ExtFinitelyGenerated.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_Resolutions

/-!
# Projective dimension at most one for finitely generated abelian groups

Every finitely generated `ℤ`-module `X` admits a free presentation `0 → K → ℤⁿ → X → 0`, and the
kernel `K`, being a submodule of a finitely generated free module over a PID, is again free.
Hence `X` has projective dimension at most one and all higher `Ext`-groups out of `X` vanish.

This generalises `Catalog.DerivedFunctors.ext_zmod_eq_zero` (the case `X = ℤ/k`).

Main results:

* `Catalog.DerivedFunctors.ext_eq_zero_of_projective_presentation`: if `X` sits in a short exact
  sequence `0 → P₁ → P₀ → X → 0` with `P₁`, `P₀` projective, then `Extⁿ⁺²(X, Y) = 0`;
* `Catalog.DerivedFunctors.free_ker_of_fin`: the kernel of a linear map `ℤⁿ → X` is a free
  `ℤ`-module;
* `Catalog.DerivedFunctors.kerShortComplex_shortExact`: the presentation `0 → ker f → M → X → 0`
  attached to a surjection `f` is short exact;
* `Catalog.DerivedFunctors.ext_fg_eq_zero`: **`Extⁿ⁺²(X, Y) = 0` for every finitely generated
  `ℤ`-module `X` and every `ℤ`-module `Y`**.
-/

open CategoryTheory Abelian Limits

namespace Catalog.DerivedFunctors



/-- The presentation short complex `0 → ker f → M → X → 0` of a linear map `f : M →ₗ[ℤ] X`. -/
noncomputable def kerShortComplex {M X : Type} [AddCommGroup M] [AddCommGroup X]
    (f : M →ₗ[ℤ] X) : ShortComplex (ModuleCat.{0} ℤ) :=
  ShortComplex.mk (ModuleCat.ofHom (LinearMap.ker f).subtype) (ModuleCat.ofHom f) (by
    ext x
    exact x.2)






end Catalog.DerivedFunctors


