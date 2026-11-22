-- Prove2me | solution 1 for Fpy.num_of_cmp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:38:17.124059+00:00
-- url     : https://prove2.me/submissions/f9f0f380-c645-45b8-b3e2-b524645086d2

import Definitions.Def_Fpy_Rewrite_Separate
import Definitions.Def_Mpfx_Rounding_Monotone
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Fpy_Rewrite_Lower

set_option autoImplicit true
open Fpy
open Mpfx
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {Γ : AEnv D} {X : Set Var}
namespace Fpy
theorem _root_.solution {σ : Store} {C : Val} {s : Bool} {t : Var} {c : Num} {v : Val}
    (h : Eval Φ σ C (.exactOp (cmpOp s) [.num c, .var t]) v) : ∃ u, σ t = some (.num u) := by
  obtain ⟨w, hx, hev⟩ : ∃ w, σ t = some w ∧ ExactOp.eval (cmpOp s) [.num c, w] = some v := by
    cases h with
    | exact hl hev => cases hl with
      | cons hc hl => cases hl with
        | cons hv hl => cases hl; cases hc; cases hv with | var hx => exact ⟨_, hx, hev⟩
  cases s <;> rcases w with _ | u | _ | _ | _ | _ <;> first | exact ⟨u, hx⟩ | cases hev
end Fpy
