-- Prove2me | solution 1 for Fpy.holds_refine_atom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:39:44.04153+00:00
-- url     : https://prove2.me/submissions/33e30181-6773-4948-957c-67414d415547

import Definitions.Def_Fpy_FormatInference_Ops
import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_FormatInference_Refine
import Theorems.Thm_Fpy_eval_parseAtom
import Theorems.Thm_Fpy_Atom_holds_refine

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx}
variable {Φ : Program (fpy decode)}
variable {c : Ceiling}
namespace Fpy
theorem _root_.solution {κ : Option Val} {e : Expr (fpy decode)} {b : Bool}
    {Γ : AEnv (Fmt.domain c)} {σ : Store} {C : Val} (hΓ : Γ.Holds σ) (hκ : Admits κ C)
    (h : Eval Φ σ C e (.bool b)) : ((parseAtom κ e).elim Γ (·.refine b Γ)).Holds σ := by
  cases ha : parseAtom κ e with
  | none => exact hΓ
  | some a =>
    obtain ⟨u, hx, hu⟩ := eval_parseAtom ha hκ h
    exact Atom.holds_refine hΓ hx hu
end Fpy
