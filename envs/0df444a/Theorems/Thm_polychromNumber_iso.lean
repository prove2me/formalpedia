-- Prove2me | Theorems.Thm_polychromNumber_iso
-- name    : polychromNumber_iso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:17.144188+00:00
-- url     : https://prove2.me/theorems/a0c969f6-efe9-4c20-a742-af28592f05a4
-- title:
--   polychrom Number iso: polychrom Number iso
-- statement:
--   The polychrom Number iso construction uses the polychrom Number iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L147-L155
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L147-L155

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_iso {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [EquivLike F G H] [AddEquivClass F G H] (φ : F)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S := by sorry
