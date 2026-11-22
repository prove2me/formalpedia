-- Prove2me | solution 1 for Fpy.exec_sumBody
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:29:35.562495+00:00
-- url     : https://prove2.me/submissions/83c5f29e-1728-4249-ab30-02b846296f64

import Definitions.Def_Fpy_Semantics
import Definitions.Def_Fpy_Ops
import Definitions.Def_Fpy_Sum
import Theorems.Thm_Fpy_sumBody_run

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
namespace Fpy
theorem _root_.solution {C : Val} {r : Num → Num} (hr : C.rnd (fpy decode) = some r)
    {us : List Num} {o : Outcome}
    (h : Exec Φ (Store.single "xs" (.list (us.map .num))) C sumBody o) :
    o = .ret (.num (sumVal r us)) :=
  Exec.det _ h (sumBody_run hr us)
end Fpy
