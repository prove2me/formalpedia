-- Prove2me | Theorems.Thm_hasPolychromColouring_neg
-- name    : hasPolychromColouring_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:35:00.673012+00:00
-- url     : https://prove2.me/theorems/0db6fba4-8186-4b86-b0d4-e1a07a09d35c
-- title:
--   has Polychrom Colouring neg: has Polychrom Colouring neg
-- statement:
--   The has Polychrom Colouring neg construction uses the has Polychrom Colouring neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L199-L201
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/Colouring.lean#L199-L201

import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Normed.Ring.Lemmas
import Definitions.Def_Polychromatic_ForMathlib_Misc
import Definitions.Def_Polychromatic_Colouring
set_option autoImplicit true
open Pointwise
variable {G : Type*} [AddCommGroup G]
variable {K : Type*}
variable {S : Finset G} {χ : G → K}
open Finset

theorem hasPolychromColouring_neg [DecidableEq G] :
    HasPolychromColouring K (-S) ↔ HasPolychromColouring K S := by sorry
