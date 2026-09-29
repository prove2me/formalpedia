-- Prove2me | solution 1 for CodiscreteMagma.cell_eq_cell
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:22:43.168082+00:00
-- url     : https://prove2.me/submissions/02fe2aed-7687-4666-8a73-72473e2c76a9

-- Sol generated from Combinatorics/CodiscreteMagmaBicategory.lean
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






lemma cell_injective : Function.Injective (cell : M → (star M ⟶ star M)) := by
  intro a b h
  exact congrArg Codiscrete.as h


/-! ### Coherence is automatic: the hom-categories are thin groupoids -/













/-! ### Every pair of 1-cells is an adjoint equivalence -/





/-! ### Strictness detects exactly the monoid axioms -/




/-! ### Functoriality on *all* set maps -/


variable {N : Type v} [Mul N] [One N]










/-! ### Collapse onto the terminal codiscrete bicategory -/








open CodiscreteMagma in
@[simp] theorem solution{a b : M} : cell a = cell b ↔ a = b :=
  ⟨fun h => cell_injective h, fun h => by rw [h]⟩
