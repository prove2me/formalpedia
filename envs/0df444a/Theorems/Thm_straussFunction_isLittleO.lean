-- Prove2me | Theorems.Thm_straussFunction_isLittleO
-- name    : straussFunction_isLittleO
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:42:59.772319+00:00
-- url     : https://prove2.me/theorems/c682e276-45e1-42e7-a455-0e67a5baf07c
-- title:
--   strauss Function is Little O: strauss Function is Little O
-- statement:
--   The strauss Function is Little O construction uses the strauss Function is Little O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L146-L153
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/LovaszFunction.lean#L146-L153

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
set_option autoImplicit true
open Finset
open Asymptotics Filter

theorem straussFunction_isLittleO :
    ∃ f : ℕ → ℝ, f =o[atTop] (fun _ ↦ 1 : ℕ → ℝ) ∧ ∀ k ≥ 4,
      straussFunction k ≤ (3 + f k) * k * Real.log k := by sorry
