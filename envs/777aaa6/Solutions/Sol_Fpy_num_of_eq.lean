-- Prove2me | solution 1 for Fpy.num_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:38:16.61406+00:00
-- url     : https://prove2.me/submissions/9f912370-ab43-4c16-80d2-937c5b6aef59

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
theorem _root_.solution {σ : Store} {C : Val} {t : Var} {c : Num} {v : Val}
    (h : Eval Φ σ C (.exactOp .eq [.var t, .num c]) v) : ∃ u, σ t = some (.num u) := by
  obtain ⟨w, hx, hev⟩ : ∃ w, σ t = some w ∧ ExactOp.eval .eq [w, .num c] = some v := by
    cases h with
    | exact hl hev => cases hl with
      | cons hv hl => cases hl with
        | cons hc hl => cases hl; cases hc; cases hv with | var hx => exact ⟨_, hx, hev⟩
  rcases w with _ | u | _ | _ | _ | _ <;> first | exact ⟨u, hx⟩ | cases hev
end Fpy
