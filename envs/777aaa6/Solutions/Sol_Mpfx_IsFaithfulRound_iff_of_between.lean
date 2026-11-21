-- Prove2me | solution 1 for Mpfx.IsFaithfulRound.iff_of_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:55:51.132162+00:00
-- url     : https://prove2.me/submissions/7ecacd6e-81ae-4323-8bcc-2f3a6877ee05

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Theorems.Thm_Mpfx_Dyadic_ext_real


set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace IsFaithfulRound
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : F₁.toFormat ⊆ F₂.toFormat) {x : ℝ} {z : Dyadic}
    (hz : IsFaithfulRound F₂ x z) (hz₁ : z ∉ F₁) (c : Dyadic) :
    IsFaithfulRound F₁ x c ↔ IsFaithfulRound F₁ z c := by
  -- A value of `F₁` at `z` would be `z` itself.
  have hne : ∀ v ∈ F₁, (v : ℝ) ≠ z := fun v hv h => hz₁ (Dyadic.ext_real h ▸ hv)
  have hle : ∀ v ∈ F₁, ((v : ℝ) ≤ x ↔ (v : ℝ) ≤ z) := fun v hv => by
    rcases hz with ⟨-, hzx, hmax⟩ | ⟨-, hxz, hmin⟩
    · exact ⟨hmax v (hsub v hv), fun h => h.trans hzx⟩
    · exact ⟨fun h => h.trans hxz, fun h => not_lt.mp fun hxv =>
        hne v hv (le_antisymm h (hmin v (hsub v hv) hxv.le))⟩
  have hge : ∀ v ∈ F₁, (x ≤ (v : ℝ) ↔ (z : ℝ) ≤ v) := fun v hv => by
    rcases hz with ⟨-, hzx, hmax⟩ | ⟨-, hxz, hmin⟩
    · exact ⟨fun h => hzx.trans h, fun h => not_lt.mp fun hvx =>
        hne v hv (le_antisymm (hmax v (hsub v hv) hvx.le) h)⟩
    · exact ⟨hmin v (hsub v hv), fun h => hxz.trans h⟩
  unfold IsFaithfulRound
  refine or_congr
    ⟨fun ⟨hc, h1, h2⟩ => ⟨hc, (hle c hc).mp h1, fun v hv h => h2 v hv ((hle v hv).mpr h)⟩,
    fun ⟨hc, h1, h2⟩ => ⟨hc, (hle c hc).mpr h1, fun v hv h => h2 v hv ((hle v hv).mp h)⟩⟩
    ⟨fun ⟨hc, h1, h2⟩ => ⟨hc, (hge c hc).mp h1, fun v hv h => h2 v hv ((hge v hv).mpr h)⟩,
    fun ⟨hc, h1, h2⟩ => ⟨hc, (hge c hc).mpr h1, fun v hv h => h2 v hv ((hge v hv).mp h)⟩⟩
end IsFaithfulRound
end Mpfx
