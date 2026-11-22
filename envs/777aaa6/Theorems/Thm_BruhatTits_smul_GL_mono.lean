-- Prove2me | Theorems.Thm_BruhatTits_smul_GL_mono
-- name    : BruhatTits.smul_GL_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:00.370441+00:00
-- url     : https://prove2.me/theorems/a466ade1-0107-48fb-bf40-a1ea871e19d9
-- title:
--   Bruhat Tits: smul GL mono
-- statement:
--   The Bruhat Tits construction uses the smul GL mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L34-L38
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L34-L38

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BruhatTits.smul_GL_mono {M L : Submodule R (ι → K)} (g : GL ι K) (hML : M ≤ L) : g • M ≤ g • L := by sorry
