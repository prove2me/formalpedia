-- Prove2me | Theorems.Thm_Catalog_Bridges_DeltaFunctor_Hom_ext_of_app_zero
-- name    : Catalog.Bridges.DeltaFunctor.Hom.ext_of_app_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:55.482102+00:00
-- url     : https://prove2.me/theorems/34122b02-6976-4fb0-9288-63d3488a739c
-- title:
--   Universality of effaceable δ-functors (uniqueness).
-- statement:
--   **Universality of effaceable δ-functors (uniqueness).**  Two morphisms of δ-functors
--   out of an effaceable δ-functor which agree in degree `0` agree in all degrees.
--
--   ```lean
--   theorem Catalog.Bridges.DeltaFunctor.Hom.ext_of_app_zero{T S : DeltaFunctor.{w} C} (hT : T.Effaceable)
--       (φ ψ : T.Hom S) (h0 : φ.app 0 = ψ.app 0) : ∀ n, φ.app n = ψ.app n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/ExtDeltaFunctor.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/ExtDeltaFunctor.lean#L112

-- Thm stub generated from Bridges/ExtDeltaFunctor.lean
import Mathlib
import Definitions.Def_Bridges_ExtDeltaFunctor

/-!
# Ext as a universal (effaceable) cohomological δ-functor

This file develops the δ-functor formalism connecting homological algebra with the
`Ext` groups computed in the derived category, and proves the *uniqueness half* of
Grothendieck's universality theorem for `Ext`.

Main contents:

* `Catalog.Bridges.DeltaFunctor` : a cohomological δ-functor on an abelian category
  `C`, i.e. a family of additive functors `F n : C ⥤ AddCommGrpCat` together with
  connecting morphisms for short exact sequences and the long exact sequence axioms;
* `Catalog.Bridges.extDeltaFunctor X` : the δ-functor `Y ↦ Ext^n(X, Y)`;
* `Catalog.Bridges.extDeltaFunctor_effaceable` : `Ext^{n+1}(X, I) = 0` for injective `I`
  (effaceability);
* `Catalog.Bridges.DeltaFunctorHom.ext_of_app_zero` : **universality (uniqueness)** —
  two morphisms of δ-functors out of an effaceable δ-functor which agree in degree `0`
  agree in every degree.  Applied to `Ext`, this says that a natural transformation
  `Hom(X, -) ⟹ S⁰` admits *at most one* extension to a morphism of δ-functors
  `Ext^*(X, -) ⟹ S^*`.
-/

universe w v u

open Catalog.Bridges

open CategoryTheory Category Limits Abelian

variable (C : Type u) [Category.{v} C] [Abelian C]


open DeltaFunctor

variable {C}





variable [EnoughInjectives C]

theorem Catalog.Bridges.DeltaFunctor.Hom.ext_of_app_zero{T S : DeltaFunctor.{w} C} (hT : T.Effaceable)
    (φ ψ : T.Hom S) (h0 : φ.app 0 = ψ.app 0) : ∀ n, φ.app n = ψ.app n := by sorry
