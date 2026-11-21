-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:44:28.147648+00:00
-- url     : https://prove2.me/submissions/b8e595af-5fe5-4c0d-b9c4-6ab240bd3dbb

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Dyadic_ext_real


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F : FiniteFormat} {d y : Dyadic} (hd : d ∈ F)
    (h : IsFaithfulRound F (d : ℝ) y) : y = d := by
  rcases h with ⟨-, hyd, hmax⟩ | ⟨-, hdy, hmin⟩
  · exact Dyadic.ext_real (le_antisymm hyd (hmax d hd le_rfl))
  · exact Dyadic.ext_real (le_antisymm (hmin d hd le_rfl) hdy)
end IsFaithfulRound
end Mpfx
