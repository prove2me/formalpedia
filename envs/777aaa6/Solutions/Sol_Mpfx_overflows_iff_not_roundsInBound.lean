-- Prove2me | solution 1 for Mpfx.overflows_iff_not_roundsInBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:37.642928+00:00
-- url     : https://prove2.me/submissions/e20385f6-45aa-4e7f-aef0-50b70578bdda

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Op_Directed
import Definitions.Def_Mpfx_Rounding_Op_ToOdd
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Definitions.Def_Mpfx_Rounding_Op
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_RoundsFinite_unique


set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {rm : RoundingMode} {x : ℝ}
    (h : ¬ F.IsUndefined rm) : Overflows F rm x ↔ ¬ ∃ y, RoundsInBound F rm x y := by
  constructor
  · rintro ⟨y, hy, hnb⟩ ⟨y', hy', hb⟩
    exact hnb (RoundsFinite.unique h hy' hy ▸ hb)
  · intro hn
    refine ⟨rndUnbounded F rm x h, rndUnbounded_satisfies F rm x h, fun hb => hn ?_⟩
    exact ⟨_, rndUnbounded_satisfies F rm x h, hb⟩
end Mpfx
