-- Prove2me | Theorems.Thm_S42Independence_five_fails_ctrl
-- name    : S42Independence.five_fails_ctrl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:43:40.327004+00:00
-- url     : https://prove2.me/theorems/637ee4e0-c1d9-4d8c-8d41-005eeb84d0f3
-- title:
--   On the control frame, `◇p → □◇p` fails for the assertion "the first button is
-- statement:
--   On the control frame, `◇p → □◇p` fails for the assertion "the first button is
--   still unpushed".
--
--   ```lean
--   theorem S42Independence.five_fails_ctrl:
--       ¬ msat ctrlFrame.rel Vunpushed
--           (.imp (MForm.dia (.atom true)) (.box (MForm.dia (.atom true)))) w₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Multiverse/S42Independence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Multiverse/S42Independence.lean#L160

-- Thm stub generated from Logic/Multiverse/S42Independence.lean
import Mathlib
import Definitions.Def_Logic_Multiverse_BooleanValuedRealization
import Definitions.Def_Logic_Multiverse_InvariantFragment
import Definitions.Def_Logic_Multiverse_S42Independence
/-
# `S4.2` Soundness for Directed Preorders, and Independence of `5` and `.3`

This file completes the calibration begun in
`Catalog/Logic/Multiverse/InvariantFragment.lean` by supplying the *deductive*
half of Direction 2 of the multiverse programme.

We define a modal language, its Kripke semantics, and a Hilbert calculus for
**`S4.2`** (classical propositional logic together with `K`, `T`, `4` and the
directedness axiom `.2`, closed under modus ponens and necessitation), and prove:

* `S42_sound` — **every theorem of `S4.2` is valid on every directed preorder**
  (induction on derivations; the `.2` case is exactly where directedness is used);
* `five_not_derivable` — the axiom `5` (`◇p → □◇p`) is **not** derivable in `S4.2`,
  because it fails on the finite button–switch forcing frame of the realization
  file, which *is* a directed preorder;
* `dot3_not_derivable` — the linearity axiom `.3`
  (`□(□p → q) ∨ □(□q → p)`) is **not** derivable in `S4.2` either: two independent
  buttons refute it.

Together with `BooleanValuedRealization.cacc_dot2` (soundness of `.2` on the frame)
and `MultiverseInvariantFragment.directed_of_dot2` (its exact semantic content),
this shows the modal logic of the finite pre-Boolean forcing frames contains `S4.2`
and is strictly below both `S5` and `S4.3`.
-/

open S42Independence

open BooleanValuedRealization MultiverseInvariantFragment

/-! ## The modal language and its Kripke semantics -/


open MForm
variable {α : Type*}



variable {α W : Type*}





/-! ## The Hilbert calculus `S4.2` -/




/-! ## The finite control frame as a directed preorder -/





/-! ## Independence of `5` -/

theorem S42Independence.five_fails_ctrl:
    ¬ msat ctrlFrame.rel Vunpushed
        (.imp (MForm.dia (.atom true)) (.box (MForm.dia (.atom true)))) w₀ := by sorry
