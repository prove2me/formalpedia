-- Prove2me | Theorems.Thm_BruhatTits_smul_eq_iff
-- name    : BruhatTits.smul_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:46.830655+00:00
-- url     : https://prove2.me/theorems/d49f4fa1-03bc-4475-9318-69cf0c241d63
-- title:
--   Bruhat Tits: smul eq iff
-- statement:
--   The Bruhat Tits construction uses the smul eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L48-L54
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L48-L54

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BruhatTits.smul_eq_iff (g : GL ι K) (M L : Submodule R (ι → K)) :
    g • M = g • L ↔ M = L := by sorry
