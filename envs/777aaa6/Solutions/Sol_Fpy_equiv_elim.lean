-- Prove2me | solution 1 for Fpy.equiv_elim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:51:07.885452+00:00
-- url     : https://prove2.me/submissions/5a26934f-3486-4e37-b6f8-01bb14142412

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_denotes_real
import Theorems.Thm_Fpy_AEnv_Holds_mem
import Theorems.Thm_Fpy_equiv_reround

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
namespace Fpy
theorem _root_.solution (hA : A.Sound Φ) {Γ : AEnv D} {C : Val} {r : Num → Num} {FC : D.Fmt}
    {x : Var} {op : L.ArithOp} {ts : List Var} {Fs : List D.Fmt}
    (hr : C.rnd L = some r) (hFC : A.ctxFmt C = some FC) (hF : FmtsIn Γ ts Fs)
    (hsub : D.γ (A.arith op Fs) ⊆ D.γ FC) :
    Equiv Φ X Γ (some C) (.assign x (.arith op (ts.map .var)))
      (.withCtx .real (.assign x (.arith op (ts.map .var)))) :=
  equiv_reround denotes_real hr rfl fun _ _ n hΓ hns hop =>
    (hA.ctxFmt hFC hr).2 n (hsub (hA.arith (hΓ.mem hF hns) hop))
end Fpy
