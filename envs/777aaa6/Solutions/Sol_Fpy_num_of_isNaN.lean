-- Prove2me | solution 1 for Fpy.num_of_isNaN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:38:13.627215+00:00
-- url     : https://prove2.me/submissions/9d90a47a-ff20-4a4a-bba5-9361a4e7dd9a

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
theorem _root_.solution {σ : Store} {C : Val} {t : Var} {v : Val}
    (h : Eval Φ σ C (.exactOp .isNaN [.var t]) v) : ∃ u, σ t = some (.num u) := by
  obtain ⟨w, hx, hev⟩ : ∃ w, σ t = some w ∧ ExactOp.eval .isNaN [w] = some v := by
    cases h with
    | exact hl hev => cases hl with
      | cons hv hl => cases hl; cases hv with | var hx => exact ⟨_, hx, hev⟩
  rcases w with _ | u | _ | _ | _ | _ <;> first | exact ⟨u, hx⟩ | cases hev
end Fpy
