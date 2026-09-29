-- Prove2me | Definitions.Def_Logic_Multiverse_InvariantFragment
-- name    : Logic_Multiverse_InvariantFragment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:58:29.162602+00:00
-- url     : https://prove2.me/theorems/772ef959-797d-4c71-98ba-7f2064b3d804
-- title:
--   Aether Catalog definitions — Logic_Multiverse_InvariantFragment
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.InvariantFragment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/InvariantFragment.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
/-
# Multiverse-Invariant Fragments, Exact Frame Calibration and Branch Preservation

This file continues `Catalog/Logic/Multiverse/BooleanValuedRealization.lean`, whose
Boolean-valued universe and control frame it takes as given, and settles three
further directions of the multiverse programme.

## 1. Exact calibration of the modal strength of the frame (Direction 2)

* `directed_of_dot2` — the schema `.2` (`◇□p → □◇p`), valid for *all* predicates,
  **implies** directedness: `.2` is exactly directedness, so nothing weaker than a
  directed frame can validate it.
* `cacc_euclidean_iff` — the forcing frame is Euclidean (i.e. validates `5`)
  **iff there are no buttons at all**.  One button already destroys `S5`.
* `dot3_fails` — with two *independent* buttons the frame refutes the linearity
  axiom `.3`.  Hence the frame sits strictly between `S4.2` and `S4.3`: it is a
  genuine `S4.2` frame, not accidentally linear.

## 2. The multiverse-invariant fragment theorem (Direction 3)

`buttonFree_invariant` shows that the **button-free fragment** is invariant under
both forcing extensions and grounds; `invariant_iff_buttonFree` proves the sharp
converse: *an assertion is invariant along the button order iff it is equivalent to
a button-free assertion*.  The proof substitutes `⊥` for every button atom
(`subBtnFls`) and uses the substitution lemma `csat_subBtnFls`.  This is a genuine
characterization, and it is falsifiable in the intended sense: a single button atom
already fails invariance (`btn_atom_not_invariant`).

## 3. Calibration of branching by preserved backgrounds (Direction 4)

The exact preservation criterion is Boolean:

* `background_branches_iff` — a background condition `b` survives into **both** a
  `p`-branch and a `¬p`-branch **iff** `b ⊓ ⟦p⟧ ≠ ⊥` and `b ⊓ ⟦p⟧ᶜ ≠ ⊥`.

Applied to the control frame this yields `button_background_branches`: every
*button-definable* background (the abstract stand-in for an indestructible
large-cardinal assertion) is preserved in both CH branches, while
`background_obstruction` exhibits the boundary — a switch-dependent background has
an empty meet with one branch and therefore cannot be preserved.
-/

namespace MultiverseInvariantFragment

open Multiverse BooleanValuedRealization

/-! ## 1. Exact calibration of the modal strength of the frame -/

section Calibration

variable {W : Type*}

/-- A relation is **Euclidean** when any two successors of a point are related;
this is the frame condition for the modal axiom `5`. -/
def EuclideanRel (R : W → W → Prop) : Prop := ∀ x y z, R x y → R x z → R y z


variable {Btn Sw : Type*}



end Calibration

/-! ## 2. The multiverse-invariant fragment -/

section Fragment

variable {Btn Sw : Type*}

/-- The **button-free fragment**: assertions built from switch atoms only. -/
inductive ButtonFree : BForm (CAtom Btn Sw) → Prop
  | atom (s : Sw) : ButtonFree (.atom (.sw s))
  | fls : ButtonFree .fls
  | imp {p q} : ButtonFree p → ButtonFree q → ButtonFree (p.imp q)



/-- Substituting `⊥` for every button atom. -/
def subBtnFls : BForm (CAtom Btn Sw) → BForm (CAtom Btn Sw)
  | .atom (.btn _) => .fls
  | .atom (.sw s) => .atom (.sw s)
  | .fls => .fls
  | .imp p q => .imp (subBtnFls p) (subBtnFls q)






end Fragment

/-! ## 3. Calibration of branching by preserved backgrounds -/

section Background

variable {α : Type*} {B : Type*} [BooleanAlgebra B]


variable {Btn Sw : Type*}





end Background

end MultiverseInvariantFragment


