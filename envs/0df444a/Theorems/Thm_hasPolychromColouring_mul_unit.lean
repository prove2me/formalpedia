-- Prove2me | Theorems.Thm_hasPolychromColouring_mul_unit
-- name    : hasPolychromColouring_mul_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:29.782679+00:00
-- url     : https://prove2.me/theorems/ed4c1cdd-134d-458e-8ac5-5e27b99d6fb2
-- title:
--   has Polychrom Colouring mul unit: has Polychrom Colouring mul unit
-- statement:
--   **Key lemma (Lemma 12(iv)).** Multiplication by a unit in ZMod m is an additive
--       automorphism, so it preserves HasPolychromColouring. Used throughout Case 1.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L621-L627
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/FourThree/Combi/CaseOne.lean#L621-L627

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)

theorem hasPolychromColouring_mul_unit (u : (ZMod m)ˣ) (S : Finset (ZMod m)) :
    HasPolychromColouring (Fin 3) (S.image (u.val * ·)) ↔
    HasPolychromColouring (Fin 3) S := by sorry
