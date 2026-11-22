-- Prove2me | solution 1 for BruhatTits.smul_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:51:49.962066+00:00
-- url     : https://prove2.me/submissions/2f9c9ee0-effa-4545-9d5c-38c0dca8a641

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Theorems.Thm_BruhatTits_smul_GL_mono

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace BruhatTits
theorem _root_.solution {M L : Submodule R (ι → K)} (g : GL ι K) : g • M ≤ g • L ↔ M ≤ L := by
  constructor
  · intro h
    rw [← one_smul (GL ι K) M, ← one_smul (GL ι K) L, ← inv_mul_cancel g, mul_smul, mul_smul]
    exact smul_GL_mono _ h
  · intro h
    exact smul_GL_mono _ h
end BruhatTits
