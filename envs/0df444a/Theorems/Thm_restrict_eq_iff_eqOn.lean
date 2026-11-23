-- Prove2me | Theorems.Thm_restrict_eq_iff_eqOn
-- name    : restrict_eq_iff_eqOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T09:18:09.01402+00:00
-- url     : https://prove2.me/theorems/8627b566-4054-4232-b668-311c7baeff62
-- title:
--   restrict eq iff eq On: restrict eq iff eq On
-- statement:
--   The restrict eq iff eq On construction uses the restrict eq iff eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L89-L91
-- source:
--   https://github.com/zksecurity/simple-rbr-fri/blob/5d99bc7bcabc7b640e063f4d75f17d8262e00a8a/SimpleRbrFri/Core.lean#L89-L91

import Mathlib
import Definitions.Def_SimpleRbrFri_Core
set_option autoImplicit true
open Polynomial
open scoped Pointwise
variable {F : Type*} [Field F] [DecidableEq F]

theorem restrict_eq_iff_eqOn {D S : Type*} (f g : D → S) (s : Set D) :
    s.restrict f = s.restrict g ↔ Set.EqOn f g s := by sorry
