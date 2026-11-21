-- Prove2me | solution 1 for Fpy.Val.isCtx_of_rnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:41:56.854007+00:00
-- url     : https://prove2.me/submissions/0899b1ad-146e-4542-a596-46e13918f919

import Definitions.Def_Fpy_Syntax
import Definitions.Def_Fpy_Semantics

set_option autoImplicit true
open Fpy
variable {L : Signature}
namespace Fpy
namespace Val
theorem _root_.solution {C : Val} {r : Num → Num} (h : C.rnd L = some r) : C.IsCtx := by
  cases C <;> trivial
end Val
end Fpy
