-- Prove2me | Theorems.Thm_hasPolychromColouring_fin_of_le
-- name    : hasPolychromColouring_fin_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:37.691058+00:00
-- url     : https://prove2.me/theorems/7817ba35-874b-4128-9fde-b2f7f1b1440c
-- title:
--   has Polychrom Colouring fin of le: has Polychrom Colouring fin of le
-- statement:
--   The has Polychrom Colouring fin of le construction uses the has Polychrom Colouring fin of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L94-L97
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L94-L97

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem hasPolychromColouring_fin_of_le {n : ℕ}
    (hn : n ≠ 0) (hS : n ≤ polychromNumber S) :
    HasPolychromColouring (Fin n) S := by sorry
