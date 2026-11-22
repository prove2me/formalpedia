-- Prove2me | solution 1 for Fpy.reals_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:32:06.895865+00:00
-- url     : https://prove2.me/submissions/3dc3a867-0b8b-4841-88bc-425620a8460d

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate

set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
namespace Fpy
theorem _root_.solution {F : Format} {u : Num} {a : ℝ} (hu : u ∈ F.reals) (h : u = .finite a) :
    ∃ d ∈ F, (d : ℝ) = a := by
  obtain ⟨w, hw, rfl⟩ := hu
  cases w with
  | finite d => exact ⟨d, hw, WithSpecial.finite.inj h⟩
  | special => cases h
end Fpy
