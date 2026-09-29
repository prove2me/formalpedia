-- Prove2me | Theorems.Thm_CodiscreteMagma_two_cell_isIso
-- name    : CodiscreteMagma.two_cell_isIso
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:04:16.850654+00:00
-- url     : https://prove2.me/theorems/d1a4fccb-f6cf-4394-80e1-a0eb6f4053dc
-- title:
--   Every 2-cell of `MagmaBicat M` is invertible.
-- statement:
--   Every 2-cell of `MagmaBicat M` is invertible.
--
--   ```lean
--   theorem CodiscreteMagma.two_cell_isIso{f g : star M ⟶ star M} (η : f ⟶ g) : IsIso η := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/CodiscreteMagmaBicategory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/CodiscreteMagmaBicategory.lean#L114

-- Thm stub generated from Combinatorics/CodiscreteMagmaBicategory.lean
import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
/-
# Codiscrete bicategories of unital magmas

For an *arbitrary* pointed magma `M` (a type with a multiplication `* : M → M → M` and a
distinguished element `1 : M`, subject to **no axioms whatsoever**) we build a bicategory
`MagmaBicat M` with a single object `⋆`, whose category of 1-cells `⋆ ⟶ ⋆` is the
*codiscrete* category on `M` (exactly one 2-cell between any two 1-cells), horizontal
composition being the magma multiplication and the identity 1-cell being `1`.

The point of the construction is that the codiscrete hom-category converts *arbitrary*
unit and associativity defects of `M` into coherent invertible 2-cells: the associator
`α_ : (a*b)*c ≅ a*(b*c)` and the unitors `λ_ : 1*a ≅ a`, `ρ_ : a*1 ≅ a` always exist and
are invertible, and the pentagon/triangle coherence equations hold automatically, because
the hom-category is thin.

Main definitions:
* `CodiscreteMagma.MagmaBicat M` : the one-object bicategory attached to a pointed magma;
* `CodiscreteMagma.star` : its unique object;
* `CodiscreteMagma.cellEquivalence` : *any* ordered pair of 1-cells is an adjoint equivalence;
* `CodiscreteMagma.mapPseudofunctor` : *any* function `M → N` (no algebraic hypothesis at all)
  induces a pseudofunctor `MagmaBicat M ⥤ᵖ MagmaBicat N`.

Main results:
* `CodiscreteMagma.two_cell_isIso`, `CodiscreteMagma.two_cell_unique` : all 2-cells are
  invertible and any two parallel 2-cells agree (coherence is automatic);
* `CodiscreteMagma.strict_iff_monoid` : the bicategory is *strict* iff the underlying pointed
  magma is a monoid.  So the construction is genuinely weak exactly when `M` has a defect;
* `CodiscreteMagma.assoc_defect_iff` / `CodiscreteMagma.unit_defect_iff` : the associator
  and the unitors are `eqToHom`s precisely at the non-defective triples/elements;
* `CodiscreteMagma.strictly_invertible_iff` : a 1-cell is *strictly* invertible iff the
  corresponding magma element has a two-sided inverse — so, unlike the 2-cell level, the
  1-cell level still remembers the algebra;
* `CodiscreteMagma.mapPseudofunctor_id`, `CodiscreteMagma.mapPseudofunctor_comp` :
  functoriality of the construction on *all* set maps.
-/

universe u v

open CategoryTheory Bicategory

open CodiscreteMagma

/-! ### The unique 2-cell of a codiscrete category -/



/-! ### The one-object bicategory of a pointed magma -/


variable (M : Type u) [Mul M] [One M]



variable {M}








/-! ### Coherence is automatic: the hom-categories are thin groupoids -/

theorem CodiscreteMagma.two_cell_isIso{f g : star M ⟶ star M} (η : f ⟶ g) : IsIso η := by sorry
