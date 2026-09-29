-- Prove2me | Definitions.Def_Novelty_Strictification
-- name    : Novelty_Strictification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:38:30.12256+00:00
-- url     : https://prove2.me/theorems/0aac9788-ab7e-4bb9-9a94-98a3e87a6215
-- title:
--   Aether Catalog definitions — Novelty_Strictification
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Strictification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Strictification.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ParenTree

/-!
# Strictification: collapsing the loops

The parenthesization category `PTree α` of `CausalLoops.ParenTree` is a genuinely
non-strict monoidal category: `(a ⊗ b) ⊗ c` and `a ⊗ (b ⊗ c)` are *distinct objects*
linked by the associator.  This file shows what "coherence" buys us: the whole tower of
loops **collapses**.

## Main results

* `PTree.ofList` — the canonical right-nested tree of a leaf-word (a *normal form* for
  bracketings).
* `PTree.normalize` — every tree is canonically isomorphic to its normal form; all
  bracketings of a word are uniquely isomorphic (Mac Lane coherence, concrete form).
* `PTree.iso_iff` — two trees are isomorphic **iff** they have the same leaf-word: the
  isomorphism class of a bracketing remembers only the underlying word.
* `PTree.flattenFunctor` — the strictification functor collapsing every bracketing to its
  word.
* `PTree.flattenFunctor_map_associator` — the associator maps to (an) identity: the loop
  is contracted by strictification.
* `PTree.strictify` — **the parenthesization category is equivalent to the discrete
  category `Discrete (List α)`**, i.e. to the strict skeleton.  A non-strict monoidal
  structure is, up to equivalence, a strict one: the "higher" data is coherent and hence
  removable.
-/

open CategoryTheory MonoidalCategory CausalLoops

namespace CausalLoops.PTree

variable {α : Type*}

/-- The canonical **right-nested** tree of a leaf-word:
`ofList [a,b,c] = a ⊗ (b ⊗ (c ⊗ nil))` after a fashion.  This is a chosen normal form
for the reassociation classes of bracketings. -/
def ofList : List α → PTree α
  | [] => nil
  | a :: rest => node (leaf a) (ofList rest)




/-- **The strictification functor.**  It sends a bracketing to its underlying leaf-word,
collapsing every reassociation to an equality in the discrete category. -/
def flattenFunctor : PTree α ⥤ Discrete (List α) where
  obj s := ⟨flatten s⟩
  map f := Discrete.eqToHom f.down
  map_id := by intros; apply Subsingleton.elim
  map_comp := by intros; apply Subsingleton.elim





end CausalLoops.PTree


