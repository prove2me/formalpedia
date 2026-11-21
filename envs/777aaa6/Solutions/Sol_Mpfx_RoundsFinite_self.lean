-- Prove2me | solution 1 for Mpfx.RoundsFinite.self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:56:45.256451+00:00
-- url     : https://prove2.me/submissions/93bece95-9c5b-4658-bdd9-a15a45774d5b

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_RoundsFinite_nearest_toEven_of_bracket
import Theorems.Thm_Mpfx_RoundsFinite_nearest_awayZero_of_bracket

set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} (rm : RoundingMode) {d : Dyadic} (hd : d ∈ F) :
    RoundsFinite F rm (d : ℝ) d := by
  have hdn : RoundsFinite F .toNegative (d : ℝ) d := ⟨hd, le_rfl, fun _ _ h => h⟩
  have hup : RoundsFinite F .toPositive (d : ℝ) d := ⟨hd, le_rfl, fun _ _ h => h⟩
  cases rm with
  | toNegative => exact hdn
  | toPositive => exact hup
  | toZero | awayZero => exact ⟨hd, le_rfl, mul_self_nonneg _, fun _ _ h _ => h⟩
  | toOdd => exact ⟨hd, .inl hdn, fun h => absurd rfl h⟩
  | nearest tb =>
    cases tb with
    | toEven =>
      exact nearest_toEven_of_bracket hdn hup (.inl rfl) ⟨le_rfl, le_rfl⟩ fun _ h => absurd rfl h
    | awayZero =>
      exact nearest_awayZero_of_bracket hdn hup (.inl rfl) ⟨le_rfl, le_rfl⟩ fun _ h => absurd rfl h
end RoundsFinite
end Mpfx
