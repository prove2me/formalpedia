-- Prove2me | Definitions.Def_Novelty_ParenTree
-- name    : Novelty_ParenTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:55:00.542897+00:00
-- url     : https://prove2.me/theorems/dd88fa31-61d6-440e-88e3-fffe364a994b
-- title:
--   Aether Catalog definitions — Novelty_ParenTree
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ParenTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ParenTree.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ThinMonoidal

/-!
# A concrete non-strict monoidal category: parenthesization trees

This file constructs an explicit *almost-category* realising the mission's central
-/
open CategoryTheory MonoidalCategory CausalLoops

namespace CausalLoops

/-- Binary trees with leaves labelled in `α`, with an empty tree `nil`.
A tree is a *formal parenthesization*: `node s t` is the bracketed product `(s · t)`. -/
inductive PTree (α : Type*) where
  | nil : PTree α
  | leaf : α → PTree α
  | node : PTree α → PTree α → PTree α
  deriving DecidableEq

namespace PTree

variable {α : Type*}

/-- The underlying leaf-word of a tree, forgetting the bracketing.
`flatten` is the "loop back" map: it sends every parenthesization of a word to the word
itself. -/
def flatten : PTree α → List α
  | nil => []
  | leaf a => [a]
  | node l r => flatten l ++ flatten r


/-- **The parenthesization category.**  Objects are trees; a morphism `s ⟶ t` is a proof
that `s` and `t` have the same underlying leaf-word.  Composition is transitivity of
equality; the identity is reflexivity.  This is the reassociation groupoid: it connects
any two bracketings of the same word by a unique isomorphism. -/
instance instCategory (α : Type*) : Category (PTree α) where
  Hom s t := PLift (flatten (α := α) s = flatten t)
  id _ := ⟨rfl⟩
  comp f g := ⟨f.down.trans g.down⟩

/-- Package an equality of leaf-words into a morphism. -/
def homOfEq {s t : PTree α} (h : flatten s = flatten t) : s ⟶ t := ⟨h⟩


/-- The parenthesization category is **thin**: there is at most one morphism between any
two trees. -/
instance instThinCategory (α : Type*) : ThinCategory (PTree α) where
  thin f g := by obtain ⟨f⟩ := f; obtain ⟨g⟩ := g; rfl

/-- Every morphism of the parenthesization category is invertible: it is a **groupoid**.
Reassociation is always reversible. -/
instance instIsIso {s t : PTree α} (f : s ⟶ t) : IsIso f :=
  ⟨homOfEq f.down.symm, ThinCategory.thin _ _, ThinCategory.thin _ _⟩

@[simp] theorem flatten_nil : flatten (nil : PTree α) = [] := rfl
@[simp] theorem flatten_leaf (a : α) : flatten (leaf a) = [a] := rfl
@[simp] theorem flatten_node (l r : PTree α) :
    flatten (node l r) = flatten l ++ flatten r := rfl

/-- Package an equality of leaf-words into an isomorphism of trees. -/
@[simps] def isoOfEq {s t : PTree α} (h : flatten s = flatten t) : s ≅ t where
  hom := homOfEq h
  inv := homOfEq h.symm
  hom_inv_id := ThinCategory.thin _ _
  inv_hom_id := ThinCategory.thin _ _

/-- The tensor data on `PTree α`: tensor of objects is `node`, the unit is `nil`, and the
associator/unitors are read off from associativity/unitality of list concatenation. -/
instance instMonoidalStruct (α : Type*) : MonoidalCategoryStruct (PTree α) where
  tensorObj := node
  whiskerLeft X _ _ f := homOfEq (congrArg (flatten X ++ ·) f.down)
  whiskerRight f Y := homOfEq (congrArg (· ++ flatten Y) f.down)
  tensorUnit := nil
  associator a b c := isoOfEq (by simp [List.append_assoc])
  leftUnitor a := isoOfEq (by simp)
  rightUnitor a := isoOfEq (by simp)


/-- **`PTree α` is a genuine monoidal category.**  Its coherence (pentagon, triangle,
naturality) is inherited *for free* from thinness via `monoidalOfThin`: because the
reassociation groupoid is contractible, there is nothing left to check. -/
instance instMonoidalCategory (α : Type*) : MonoidalCategory (PTree α) :=
  monoidalOfThin (PTree α)





end PTree

end CausalLoops


