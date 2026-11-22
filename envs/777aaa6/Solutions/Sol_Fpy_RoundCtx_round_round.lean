-- Prove2me | solution 1 for Fpy.RoundCtx.round_round
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:52:23.76123+00:00
-- url     : https://prove2.me/submissions/957450db-d95e-4913-8a54-95002812eb58

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
import Theorems.Thm_Fpy_RoundCtx_round_round_of_rnd

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy
namespace RoundCtx
theorem _root_.solution {c₁ c₂ : RoundCtx}
    (h : ∀ v u, rnd c₂.F c₂.S c₂.O c₂.rm v = .value u →
      rnd c₁.F c₁.S c₁.O c₁.rm u.toReal = rnd c₁.F c₁.S c₁.O c₁.rm v) (n : Num) :
    c₁.round (c₂.round n) = c₁.round n :=
  round_round_of_rnd (h n)
end RoundCtx
end Fpy
