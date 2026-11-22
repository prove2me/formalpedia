-- Prove2me | Theorems.Thm_polychromNumber_le_of_forall
-- name    : polychromNumber_le_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:12.962062+00:00
-- url     : https://prove2.me/theorems/26e17823-96b5-4685-8bfd-354574697843
-- title:
--   polychrom Number le of forall: polychrom Number le of forall
-- statement:
--   The polychrom Number le of forall construction uses the polychrom Number le of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L261-L266
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L261-L266

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_le_of_forall {S : Finset G} {k : ℕ}
    (h : ∀ χ : G → Fin (k + 1), ¬ IsPolychrom S χ) :
    polychromNumber S ≤ k := by sorry
