-- Prove2me | Theorems.Thm_le_polychromNumber_iff_hasPolychromColouring
-- name    : le_polychromNumber_iff_hasPolychromColouring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:54.607814+00:00
-- url     : https://prove2.me/theorems/a693a2b5-7701-4547-94d0-8a86715e1e38
-- title:
--   le polychrom Number iff has Polychrom Colouring: le polychrom Number iff has Polychrom Colouring
-- statement:
--   The le polychrom Number iff has Polychrom Colouring construction uses the le polychrom Number iff has Polychrom Colouring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L107-L111
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L107-L111

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem le_polychromNumber_iff_hasPolychromColouring {n : ℕ} (hn : n ≠ 0) {S : Finset G} :
    n ≤ polychromNumber S ↔ HasPolychromColouring (Fin n) S := by sorry
