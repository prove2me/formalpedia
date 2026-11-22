-- Prove2me | Theorems.Thm_Subtype_val_comp_single
-- name    : Subtype.val_comp_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:40:44.825354+00:00
-- url     : https://prove2.me/theorems/4cd6003e-2ea0-4faa-9c5a-1e4562f4f64c
-- title:
--   Subtype: val comp single
-- statement:
--   The Subtype construction uses the val comp single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L23-L27
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Subring.lean#L23-L27

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

theorem Subtype.val_comp_single (i : ι) (a : A) :
    Subtype.val ∘ Pi.single i a = Pi.single i a := by sorry
