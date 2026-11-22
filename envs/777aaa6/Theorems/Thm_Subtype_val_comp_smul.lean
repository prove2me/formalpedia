-- Prove2me | Theorems.Thm_Subtype_val_comp_smul
-- name    : Subtype.val_comp_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:41:05.231312+00:00
-- url     : https://prove2.me/theorems/5d085732-1f9c-4e2d-9c2b-daed1f9c6269
-- title:
--   Subtype: val comp smul
-- statement:
--   The Subtype construction uses the val comp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L37-L41
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L37-L41

import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Basis.Submodule
import Definitions.Def_BruhatTits_Utils_Subring
set_option autoImplicit false
universe uCompat vCompat wCompat
variable {ι : Type*} [DecidableEq ι]
variable {R : Type*} [Ring R]
variable {A : Subring R}
omit [DecidableEq ι]

theorem Subtype.val_comp_smul (a : A) (v : ι → A) :
    Subtype.val ∘ (a • v) = a • Subtype.val ∘ v := by sorry
