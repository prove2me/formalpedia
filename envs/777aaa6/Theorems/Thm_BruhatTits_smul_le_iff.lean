-- Prove2me | Theorems.Thm_BruhatTits_smul_le_iff
-- name    : BruhatTits.smul_le_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:50:33.727806+00:00
-- url     : https://prove2.me/theorems/01184704-865b-4e89-93cd-c304e6704919
-- title:
--   Bruhat Tits: smul le iff
-- statement:
--   The Bruhat Tits construction uses the smul le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L40-L46
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L40-L46

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BruhatTits.smul_le_iff {M L : Submodule R (ι → K)} (g : GL ι K) : g • M ≤ g • L ↔ M ≤ L := by sorry
