-- Prove2me | solution 1 for Mpfx.RoundsFinite.unique_toOdd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:50.484779+00:00
-- url     : https://prove2.me/submissions/2264ef91-8301-4db0-9846-9308a88b49db

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_isFaithfulRound_iff_directed
import Theorems.Thm_Mpfx_RoundsFinite_unique_toNegative
import Theorems.Thm_Mpfx_RoundsFinite_unique_toPositive
import Theorems.Thm_Mpfx_isOdd_alternate_of_bracketing
import Theorems.Thm_Mpfx_Dyadic_ext_real


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution {F : FiniteFormat} {x : ℝ}
    (h : ¬ F.IsUndefined .toOdd) {y₁ y₂ : Dyadic}
    (h₁ : RoundsFinite F.unbounded .toOdd x y₁)
    (h₂ : RoundsFinite F.unbounded .toOdd x y₂) :
    y₁ = y₂ := by
  obtain ⟨-, hf₁, hp₁⟩ := h₁
  obtain ⟨-, hf₂, hp₂⟩ := h₂
  -- `a` rounds down, `b` rounds up. Symmetric, so proved once.
  have mixed : ∀ {a b : Dyadic},
      RoundsFinite F.unbounded .toNegative x a →
      RoundsFinite F.unbounded .toPositive x b →
      (x ≠ (a : ℝ) → F.IsOdd a) → (x ≠ (b : ℝ) → F.IsOdd b) →
      a = b := by
    intro a b hda hub hpa hpb
    obtain ⟨ha_mem, ha_le, ha_max⟩ := id hda
    obtain ⟨hb_mem, hb_ge, hb_min⟩ := id hub
    by_cases hxa : x = (a : ℝ)
    · exact Dyadic.ext_real (le_antisymm (hxa ▸ hb_ge) (hb_min a ha_mem hxa.le))
    by_cases hxb : x = (b : ℝ)
    · exact Dyadic.ext_real (le_antisymm (hxb ▸ ha_le) (ha_max b hb_mem hxb.ge))
    exfalso
    exact (isOdd_alternate_of_bracketing (F := F.unbounded) h hda hub hxa).mp (hpb hxb) (hpa hxa)
  rcases isFaithfulRound_iff_directed.mp hf₁ with hd₁ | hu₁ <;>
    rcases isFaithfulRound_iff_directed.mp hf₂ with hd₂ | hu₂
  · exact RoundsFinite.unique_toNegative hd₁ hd₂
  · exact mixed hd₁ hu₂ hp₁ hp₂
  · exact (mixed hd₂ hu₁ hp₂ hp₁).symm
  · exact RoundsFinite.unique_toPositive hu₁ hu₂
end RoundsFinite
end Mpfx
