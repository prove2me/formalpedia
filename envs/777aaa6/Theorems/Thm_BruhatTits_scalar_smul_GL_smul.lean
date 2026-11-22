-- Prove2me | Theorems.Thm_BruhatTits_scalar_smul_GL_smul
-- name    : BruhatTits.scalar_smul_GL_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:45.487243+00:00
-- url     : https://prove2.me/theorems/96f051b3-e8a0-46de-b622-a41271ce98ca
-- title:
--   Bruhat Tits: scalar smul GL smul
-- statement:
--   The Bruhat Tits construction uses the scalar smul GL smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L16-L32
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L16-L32

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BruhatTits.scalar_smul_GL_smul (M : Submodule R (ι → K))
    (a : K) (g : GL ι K) : a • g • M = g • a • M := by sorry
