-- Prove2me | Theorems.Thm_Subtype_val_comp_add
-- name    : Subtype.val_comp_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:59.053044+00:00
-- url     : https://prove2.me/theorems/5575a64c-3b58-4b8e-a5f5-894384efc5c2
-- title:
--   Subtype: val comp add
-- statement:
--   The Subtype construction uses the val comp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L31-L34
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L31-L34

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

theorem Subtype.val_comp_add (v w : ι → A) :
    Subtype.val ∘ (v + w) = Subtype.val ∘ v + Subtype.val ∘ w := by sorry
