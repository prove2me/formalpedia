-- Prove2me | Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
-- name    : Combinatorics_CodiscreteMagmaBicategory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:30:23.657405+00:00
-- url     : https://prove2.me/theorems/60d36b7a-90b1-48a8-a95e-1049bb3aa0b2
-- title:
--   Aether Catalog definitions — Combinatorics_CodiscreteMagmaBicategory
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.CodiscreteMagmaBicategory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/CodiscreteMagmaBicategory.lean by skeleton subtraction
import Mathlib
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

namespace CodiscreteMagma

/-! ### The unique 2-cell of a codiscrete category -/

/-- The unique isomorphism between two objects of a codiscrete category. -/
def codIso {A : Type u} (x y : Codiscrete A) : x ≅ y where
  hom := ⟨⟩
  inv := ⟨⟩
  hom_inv_id := rfl
  inv_hom_id := rfl


/-! ### The one-object bicategory of a pointed magma -/

/-- The one-object bicategory attached to a pointed magma `M`: its unique object is `star`,
its 1-cells are the elements of `M`, and its 2-cells form the codiscrete category on `M`. -/
@[nolint unusedArguments]
def MagmaBicat (M : Type u) [Mul M] [One M] : Type := PUnit

variable (M : Type u) [Mul M] [One M]

instance : Inhabited (MagmaBicat M) := ⟨PUnit.unit⟩

/-- The unique object of `MagmaBicat M`. -/
def star : MagmaBicat M := PUnit.unit

variable {M}

instance magmaBicategory : Bicategory (MagmaBicat M) where
  Hom _ _ := Codiscrete M
  id _ := ⟨1⟩
  comp f g := ⟨f.as * g.as⟩
  whiskerLeft := by intros; exact PUnit.unit
  whiskerRight := by intros; exact PUnit.unit
  associator _ _ _ := codIso _ _
  leftUnitor _ := codIso _ _
  rightUnitor _ := codIso _ _
  whiskerLeft_id := by intros; rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; rfl
  comp_whiskerLeft := by intros; rfl
  id_whiskerRight := by intros; rfl
  comp_whiskerRight := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerRight_comp := by intros; rfl
  whisker_assoc := by intros; rfl
  whisker_exchange := by intros; rfl
  pentagon := by intros; rfl
  triangle := by intros; rfl

/-- The 1-cell of `MagmaBicat M` named by an element of `M`. -/
def cell (a : M) : star M ⟶ star M := ⟨a⟩






/-! ### Coherence is automatic: the hom-categories are thin groupoids -/

/-- Any two parallel 2-cells of `MagmaBicat M` are equal: every coherence diagram commutes. -/
theorem two_cell_unique {f g : star M ⟶ star M} (η θ : f ⟶ g) : η = θ := rfl



/-- The canonical invertible 2-cell repairing the associativity defect at `(a, b, c)`. -/
def assocDefectIso (a b c : M) : cell ((a * b) * c) ≅ cell (a * (b * c)) := codIso _ _

/-- The canonical invertible 2-cell repairing the left unit defect at `a`. -/
def leftUnitDefectIso (a : M) : cell ((1 : M) * a) ≅ cell a := codIso _ _

/-- The canonical invertible 2-cell repairing the right unit defect at `a`. -/
def rightUnitDefectIso (a : M) : cell (a * (1 : M)) ≅ cell a := codIso _ _







/-! ### Every pair of 1-cells is an adjoint equivalence -/

/-- **Codiscreteness trivialises invertibility at the 1-cell level up to iso**: for *any* two
elements `a b : M` — with no algebraic relation between them whatsoever — the 1-cells they name
form an adjoint equivalence of the unique object of `MagmaBicat M` with itself. -/
def cellEquivalence (a b : M) : Bicategory.Equivalence (star M) (star M) where
  hom := cell a
  inv := cell b
  unit := codIso _ _
  counit := codIso _ _
  left_triangle := Iso.ext (two_cell_unique _ _)




/-! ### Strictness detects exactly the monoid axioms -/

/-- **The strictness criterion.**  `MagmaBicat M` is a strict bicategory (a 2-category) if and
only if the pointed magma `M` is a monoid.  Every genuine unit or associativity defect of `M`
therefore produces a bicategory that is weak but coherent. -/
theorem strict_iff_monoid :
    Bicategory.Strict (MagmaBicat M) ↔
      ((∀ a b c : M, (a * b) * c = a * (b * c)) ∧ (∀ a : M, (1 : M) * a = a) ∧
        ∀ a : M, a * (1 : M) = a) := by
  constructor
  · intro h
    refine ⟨fun a b c => ?_, fun a => ?_, fun a => ?_⟩
    · exact congrArg Codiscrete.as (h.assoc (cell a) (cell b) (cell c))
    · exact congrArg Codiscrete.as (h.id_comp (cell a))
    · exact congrArg Codiscrete.as (h.comp_id (cell a))
  · rintro ⟨hassoc, hone, hone'⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ f; exact Codiscrete.ext (hone f.as)
    · intro _ _ f; exact Codiscrete.ext (hone' f.as)
    · intro _ _ _ _ f g h; exact Codiscrete.ext (hassoc f.as g.as h.as)
    · intro _ _ f; exact Iso.ext (two_cell_unique _ _)
    · intro _ _ f; exact Iso.ext (two_cell_unique _ _)
    · intro _ _ _ _ f g h; exact Iso.ext (two_cell_unique _ _)

/-- A monoid gives a strict bicategory. -/
instance strict_of_monoid {M : Type u} [Monoid M] : Bicategory.Strict (MagmaBicat M) :=
  (strict_iff_monoid).2 ⟨fun a b c => (mul_assoc a b c), fun a => one_mul a, fun a => mul_one a⟩


/-! ### Functoriality on *all* set maps -/

section Functoriality

variable {N : Type v} [Mul N] [One N]

/-- **Any** function `f : M → N` — not required to preserve the multiplication or the unit —
induces a pseudofunctor between the codiscrete bicategories.  This is the precise sense in
which the codiscrete construction only sees the underlying pointed set. -/
def mapPseudofunctor (f : M → N) : Pseudofunctor (MagmaBicat M) (MagmaBicat N) where
  obj _ := star N
  map g := cell (f g.as)
  map₂ := by intros; exact PUnit.unit
  map₂_id := by intros; rfl
  map₂_comp := by intros; rfl
  mapId _ := codIso _ _
  mapComp _ _ := codIso _ _
  map₂_whisker_left := by intros; rfl
  map₂_whisker_right := by intros; rfl
  map₂_associator := by intros; rfl
  map₂_left_unitor := by intros; rfl
  map₂_right_unitor := by intros; rfl








end Functoriality

/-! ### Collapse onto the terminal codiscrete bicategory -/

section Collapse

/-- The pseudofunctor collapsing `MagmaBicat M` onto the one-point magma. -/
def toTerminal : Pseudofunctor (MagmaBicat M) (MagmaBicat PUnit) :=
  mapPseudofunctor fun _ => PUnit.unit

/-- The pseudofunctor picking out the identity 1-cell of `MagmaBicat M`. -/
def fromTerminal : Pseudofunctor (MagmaBicat PUnit) (MagmaBicat M) :=
  mapPseudofunctor fun _ => (1 : M)



end Collapse

end CodiscreteMagma


