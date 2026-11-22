-- Prove2me | Theorems.Thm_polychromNumber_univ
-- name    : polychromNumber_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:40:30.329331+00:00
-- url     : https://prove2.me/theorems/ac59aa13-7eb2-44d1-993e-98ed19c4517c
-- title:
--   polychrom Number univ: polychrom Number univ
-- statement:
--   The polychrom Number univ construction uses the polychrom Number univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L130-L134
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L130-L134

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_univ [Fintype G] :
    polychromNumber (univ : Finset G) = Fintype.card G := by sorry
