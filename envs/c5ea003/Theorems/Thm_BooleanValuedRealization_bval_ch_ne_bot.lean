-- Prove2me | Theorems.Thm_BooleanValuedRealization_bval_ch_ne_bot
-- name    : BooleanValuedRealization.bval_ch_ne_bot
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:05.502237+00:00
-- url     : https://prove2.me/theorems/fdfd62b7-9385-4156-9cba-cfbae30af54b
-- title:
--   The Boolean value of CH is nonzero: some generic object makes CH true.
-- statement:
--   The Boolean value of CH is nonzero: some generic object makes CH true.
--
--   ```lean
--   theorem BooleanValuedRealization.bval_ch_ne_bot(S : Finset Btn) (s : Sw) :
--       bval (cassign (Btn := Btn) S) (chAtom s) ≠ ⊥ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/BooleanValuedRealization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/BooleanValuedRealization.lean#L544

-- Thm stub generated from Logic/Multiverse/BooleanValuedRealization.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_ButtonsSwitches
/-
# Internal Boolean-Valued Realization of the Forcing Multiverse

This file answers *Direction 1* of the multiverse research programme: it builds a
**Boolean-valued universe whose generic quotients instantiate the abstract forcing
frame**, with forcing closure, directedness and the two opposite Continuum
Hypothesis branches **derived** from the construction rather than assumed as frame
axioms.

The development has four layers.

## Layer A — Boolean-valued semantics and generic quotients

Over an arbitrary Boolean algebra `B` we give the Boolean value `bval v p ∈ B` of a
propositional set-theoretic assertion `p`, define a **generic filter** (a proper
filter deciding every element), and prove the **truth lemma**

* `sat_quot_iff` : `sat (quot v U) p ↔ U.mem (bval v p)` ,

the propositional core of the Boolean-valued-model quotient theorem: the two-valued
quotient satisfies exactly the assertions whose Boolean value lies in the generic
filter.  Around it:

* `bval_eq_top_of_provable` — **forcing closure**: every theorem of classical
  propositional logic has Boolean value `⊤` (soundness of Boolean-valued semantics
  for a Hilbert calculus, by induction on derivations);
* `sat_quot_of_provable`, `sat_quot_of_forces` — everything forced by a condition
  in the generic filter is true in the quotient;
* `branch_of_undecided` — **branching**: an assertion whose Boolean value is
  neither `⊥` nor `⊤` is *true in one generic quotient and false in another*.

## Layer B — the pre-Boolean control frame of buttons and switches

Worlds are pairs `(S, g)` with `S` a finite set of *pushed buttons* and `g` a
setting of the *switches*; accessibility is `S ⊆ T`.  The frame is reflexive,
transitive and **directed** (`cacc_directed`), hence sound for `S4.2`
(`cacc_T`, `cacc_four`, `cacc_dot2`); pushed buttons are buttons in the sense of
`Catalog/Logic/Multiverse/ButtonsSwitches.lean` (`pushed_is_button`) and switches
are switches (`switch_is_switch`).

## Layer C — the realization: Layer B *is* the generic-quotient frame of Layer A

The Boolean algebra is the powerset `Set (Sw → Bool)` of switch settings; stage `S`
carries the assignment `cassign S`, and the generic filters used are the principal
ones at a generic point `g`.  The main theorem

* `realization` : `csat (S, g) p ↔ g ∈ bval (cassign S) p`

says that the control world `(S, g)` is *exactly* the generic quotient of the
Boolean-valued universe at stage `S` by the generic object `g`.  Consequently:

* `button_of_pos` — every **positive button formula** defines a button, *derived*
  from Boolean-valued monotonicity `bval_mono_of_pos`, not assumed;
* `cassign_union_btn` — amalgamation of stages on the algebra side, matching frame
  directedness;
* `CH_branches_derived` — both CH branches come from `branch_of_undecided` applied
  to the CH switch, whose Boolean value is provably neither `⊥` nor `⊤`;
* `five_fails`, `brouwer_fails` — the realized frame validates `.2` yet refutes
  `5` and `B`, so it is genuinely an `S4.2` frame.

## Layer D — ground/extension bimodality

Adding the converse **ground** modality we prove the mixed tense validity
`p → □ ◇̌ p` (`tense_axiom_valid`) while the unimodal Brouwer analogue `p → □ ◇ p`
**fails** on the very same frame (`brouwer_fails`): a concrete separation of the
mixed logic from the extension-only logic (`bimodal_separation`).  Grounds are
downward directed and possess a least element, the **mantle** (`mantle_least`).
-/

open BooleanValuedRealization

open Multiverse

/-! ## Layer A.1 — syntax and Boolean values -/


open BForm
variable {α : Type*}



variable {α : Type*} {B : Type*} [BooleanAlgebra B]







/-! ## Layer A.2 — forcing closure: soundness of Boolean-valued semantics -/


variable (a b c : B)







/-! ## Layer A.3 — generic filters and the truth lemma -/


open Generic
variable (U : Generic B)
















/-! ## Layer A.4 — branching -/






/-! ## Layer B — the pre-Boolean control frame of buttons and switches -/


variable {Btn Sw : Type*}






/-! ### `S4.2` soundness of the control frame -/





/-! ### Buttons and switches -/






/-! ### Failure of `5`: the frame is `S4.2`, not `S5` -/




/-! ## Layer C — the Boolean-valued realization of the control frame -/


variable {Btn Sw : Type*}









/-! ### Positive button formulas and derived forcing closure -/






/-! ### The Continuum Hypothesis branches, derived -/

theorem BooleanValuedRealization.bval_ch_ne_bot(S : Finset Btn) (s : Sw) :
    bval (cassign (Btn := Btn) S) (chAtom s) ≠ ⊥ := by sorry
