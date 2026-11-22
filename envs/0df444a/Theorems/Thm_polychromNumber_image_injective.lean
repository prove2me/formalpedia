-- Prove2me | Theorems.Thm_polychromNumber_image_injective
-- name    : polychromNumber_image_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:41:12.803181+00:00
-- url     : https://prove2.me/theorems/9956cd67-d827-4df3-ab60-286be3c040c7
-- title:
--   polychrom Number image injective: polychrom Number image injective
-- statement:
--   The polychrom Number image injective construction uses the polychrom Number image injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L200-L206
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/PolychromNumber.lean#L200-L206

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise

theorem polychromNumber_image_injective {H : Type*} [DecidableEq H] [AddCommGroup H]
    {F : Type*} [FunLike F G H] [AddMonoidHomClass F G H] (φ : F) (hφ : Function.Injective φ)
    {S : Finset G} :
    polychromNumber (S.image φ) = polychromNumber S := by sorry
