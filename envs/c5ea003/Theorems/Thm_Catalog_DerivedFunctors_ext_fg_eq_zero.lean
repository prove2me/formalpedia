-- Prove2me | Theorems.Thm_Catalog_DerivedFunctors_ext_fg_eq_zero
-- name    : Catalog.DerivedFunctors.ext_fg_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:47.837045+00:00
-- url     : https://prove2.me/theorems/1d91c76c-b904-40bc-b00e-46c8e26126ba
-- title:
--   Finitely generated abelian groups have projective dimension at most one.
-- statement:
--   **Finitely generated abelian groups have projective dimension at most one.**
--   For every finitely generated `ℤ`-module `X`, every `ℤ`-module `Y` and every `n`,
--   `Extⁿ⁺²(X, Y) = 0`.
--
--   ```lean
--   theorem Catalog.DerivedFunctors.ext_fg_eq_zero(X : Type) [AddCommGroup X] [Module.Finite ℤ X]
--       (Y : ModuleCat.{0} ℤ) (n : ℕ) (x : Ext (ModuleCat.of ℤ X) Y (n + 2)) : x = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/DerivedFunctors/ExtFinitelyGenerated.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/DerivedFunctors/ExtFinitelyGenerated.lean#L73

-- Thm stub generated from Algebra/DerivedFunctors/ExtFinitelyGenerated.lean
import Mathlib
import Definitions.Def_Algebra_DerivedFunctors_ExtFinitelyGenerated
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

open Catalog.DerivedFunctors

theorem Catalog.DerivedFunctors.ext_fg_eq_zero(X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (Y : ModuleCat.{0} ℤ) (n : ℕ) (x : Ext (ModuleCat.of ℤ X) Y (n + 2)) : x = 0 := by sorry
