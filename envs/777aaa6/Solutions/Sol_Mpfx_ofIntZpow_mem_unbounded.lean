-- Prove2me | solution 1 for Mpfx.ofIntZpow_mem_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:40:55.778024+00:00
-- url     : https://prove2.me/submissions/0b16344d-143f-4ba3-86cd-9c4884db4e71

import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_CanonicalExp
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_of_abs_le
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_b
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_b



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) {k e : ℤ}
    (he_ge : ∀ {e' : ℤ}, F.exp = (e' : QExp) → e' ≤ e)
    (hk_bound : ∀ {p : ℕ}, F.p = (p : Prec) →
      |k| ≤ (2 : ℤ) ^ p) :
    Dyadic.ofIntZpow k e ∈ F.unbounded := by
  refine ⟨?_, ?_, ?_⟩
  · change Dyadic.precisionAtMost F.p (Dyadic.ofIntZpow k e)
    cases hp : F.p using ENat.recTopCoe with
    | top => trivial
    | coe p =>
      exact Dyadic.precisionAtMost_of_abs_le (F.p_pos hp) k e
        (Dyadic.coe_rat_ofIntZpow k e) (hk_bound hp)
  · refine Dyadic.quantumAtLeast_ofIntZpow ?_
    cases hexp : F.unbounded.exp using QExp.recBotCoe with
    | bot => exact bot_le
    | coe e' => exact WithBot.coe_le_coe.mpr (he_ge hexp)
  · change Format.boundOK F.unbounded.b (Dyadic.ofIntZpow k e)
    rw [FiniteFormat.unbounded_b]; trivial
end Mpfx
