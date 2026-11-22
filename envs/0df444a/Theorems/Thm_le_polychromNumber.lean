-- Prove2me | Theorems.Thm_le_polychromNumber
-- name    : le_polychromNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:34.304467+00:00
-- url     : https://prove2.me/theorems/a93f8c24-e5d4-4141-bb83-a2a1140ec2a6
-- title:
--   le polychrom Number: le polychrom Number
-- statement:
--   If a `Fin n`-valued polychromatic colouring exists, then `n ≤ polychromNumber S`.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L62-L64
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L62-L64

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem le_polychromNumber {n : ℕ} (hn : HasPolychromColouring (Fin n) S) :
    n ≤ polychromNumber S := by sorry
