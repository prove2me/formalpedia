-- Prove2me | Definitions.Def_Logic_Multiverse_ButtonsSwitches
-- name    : Logic_Multiverse_ButtonsSwitches
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:54.592554+00:00
-- url     : https://prove2.me/theorems/940bb032-f462-4f2b-be9a-58f9d9d563c4
-- title:
--   Aether Catalog definitions — Logic_Multiverse_ButtonsSwitches
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Multiverse.ButtonsSwitches`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Multiverse/ButtonsSwitches.lean by skeleton subtraction
import Mathlib

/-!
# Buttons and Switches in the Forcing Multiverse

Direction 2 of the research programme.  On a forcing frame `(W, R)` an *assertion*
is a predicate `P : W → Prop`.  Following Hamkins:

* a **button** is an assertion that, once true, stays necessarily true — i.e. it is
  *monotone* along the accessibility order;
* a **switch** is an assertion such that both it and its negation remain *possible*
  from every world.

We prove:

* `button_iff_box_fixed` — over a **reflexive** frame the buttons are *exactly*
  the fixed points of the necessity operator `□` (`box R P = P`).
* `button_and`, `button_or` — buttons are closed under conjunction and disjunction,
  and (`button_distrib`) satisfy the distributive law, so they form a distributive
  lattice.
* `switch_iff_nonconstant_of_complete` — in the *fully connected* multiverse
  (every world accesses every world, the finite-information equivalence frame) the
  switches are exactly the non-constant assertions: forcing can toggle any
  contingent statement, the Continuum Hypothesis included.
* `switch_not_button` — a genuine switch (which is possibly-false somewhere) is
  never a non-trivial button.
-/

namespace Multiverse

variable {W : Type*} (R : W → W → Prop)

/-- Necessity: `p` holds in every world accessible from `w`. -/
def box (P : W → Prop) (w : W) : Prop := ∀ v, R w v → P v

/-- Possibility: `p` holds in some world accessible from `w`. -/
def dia (P : W → Prop) (w : W) : Prop := ∃ v, R w v ∧ P v

/-- A **button**: monotone along accessibility.  Once `P` becomes true it is true
in every further extension. -/
def Button (P : W → Prop) : Prop := ∀ ⦃w v⦄, R w v → P w → P v

/-- A **switch**: from every world both `P` and `¬P` are still possible. -/
def Switch (P : W → Prop) : Prop := ∀ w, dia R P w ∧ dia R (fun x => ¬ P x) w

/-! ## Buttons are the fixed points of `□` -/


/-
Buttons are closed under conjunction.
-/

/-
Buttons are closed under disjunction.
-/

/-
The lattice of buttons is distributive (pointwise Boolean distributivity).
-/

/-! ## Switches in the fully connected multiverse -/

/-- The **complete** accessibility relation: every world accesses every world.
This models the finite-information equivalence frame in which any generic
extension is reachable from any other. -/
def completeRel (W : Type*) : W → W → Prop := fun _ _ => True

/-
In the (nonempty) complete multiverse, an assertion is a switch iff it is
non-constant: there is a world where it holds and a world where it fails.
-/

/-
A genuine switch is never a non-trivial button: if `P` is both a switch and a
button, then `P` is contradictory (false everywhere), so no contingent assertion
can be both.
-/

end Multiverse


