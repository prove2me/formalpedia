-- Prove2me | solution 1 for Mpfx.Format.exp_le_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:09.763236+00:00
-- url     : https://prove2.me/submissions/76052802-3f09-4b59-a65f-0bc8f3b0d32c

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Dyadic_abs_ge_two_zpow_of_quantum
import Theorems.Thm_Mpfx_Format_Nontrivial_p_ne_zero
import Theorems.Thm_Mpfx_Format_ofIntZpow_mem
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow
import Theorems.Thm_Mpfx_quantum_le_of_odd_rep

section
namespace Mpfx
namespace Format
private theorem exists_mul_zpow_le {C r : ℝ} (hC : 0 < C) (hr : 0 < r) (e : ℤ) :
    ∃ k : ℤ, k ≤ e ∧ C * (2 : ℝ) ^ k ≤ r := by
  refine ⟨min e (Int.log 2 (r / C)), min_le_left _ _, ?_⟩
  have h1 : (2 : ℝ) ^ (min e (Int.log 2 (r / C))) ≤ (2 : ℝ) ^ (Int.log 2 (r / C)) :=
    zpow_le_zpow_right₀ (by norm_num) (min_le_right _ _)
  have h2 : (2 : ℝ) ^ (Int.log 2 (r / C)) ≤ r / C :=
    Int.zpow_log_le_self (by norm_num : (1 : ℕ) < 2) (div_pos hr hC)
  calc C * (2 : ℝ) ^ (min e (Int.log 2 (r / C))) ≤ C * (r / C) := by nlinarith
    _ = r := by field_simp
end Format
namespace FiniteFormat
end FiniteFormat
namespace Format
end Format
namespace FiniteFormat
end FiniteFormat
namespace Format
end Format
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F₁ F₂ : Format} (hnt : F₁.Nontrivial) (h : F₁ ⊆ F₂) :
    F₂.exp ≤ F₁.exp := by
  have hp0 := hnt.p_ne_zero
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hnt
  cases he2 : F₂.exp using QExp.recBotCoe with
  | bot => exact bot_le
  | coe e₂ =>
    -- `2^k ∈ F₁` forces `e₂ ≤ k`, since `F₂`'s values are multiples of `2^e₂`.
    have key : ∀ k : ℤ, Dyadic.ofIntZpow 1 k ∈ F₁ → e₂ ≤ k := by
      intro k hk
      have hq := (h _ hk).2.1
      rw [he2] at hq
      exact quantum_le_of_odd_rep hq odd_one (by rw [coe_real_ofIntZpow_one]; norm_num)
    cases he1 : F₁.exp using QExp.recBotCoe with
    | coe e₁ =>
      -- `2^e₁ ≤ |x₀| ≤ b₁`, so `2^e₁` is in bound.
      refine WithBot.coe_le_coe.mpr (key e₁ (ofIntZpow_mem
        (precisionAtMost_one_zpow hp0 e₁)
        (by rw [he1]) (boundOK_of_abs_le ?_ hx₀.2.2)))
      rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) e₁)]
      exact Dyadic.abs_ge_two_zpow_of_quantum (he1 ▸ hx₀.2.1) (by exact_mod_cast hx₀ne)
    | bot =>
      -- `F₁` has values `2^k` with `k` arbitrarily small, contradicting `e₂ ≤ k`.
      exfalso
      obtain ⟨k, hk_le, hk_bnd⟩ :
          ∃ k : ℤ, k ≤ e₂ - 1 ∧ boundOK F₁.b (Dyadic.ofIntZpow 1 k) := by
        cases hb1 : F₁.b using Bound.recTopCoe with
        | top => exact ⟨e₂ - 1, le_refl _, trivial⟩
        | coe b₁ =>
          have hpos : 0 < ((b₁.val : Dyadic) : ℝ) :=
            lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hx₀ne))
              (abs_coe_real_le_of_boundOK (hb1 ▸ hx₀.2.2))
          obtain ⟨k, hk_le, hk⟩ := exists_mul_zpow_le one_pos hpos (e₂ - 1)
          refine ⟨k, hk_le, boundOK_coe_of_abs_le ?_⟩
          rw [coe_real_ofIntZpow_one, abs_of_pos (zpow_pos (by norm_num) k)]
          linarith
      have := key k (ofIntZpow_mem (precisionAtMost_one_zpow hp0 k)
        (by rw [he1]; exact bot_le) hk_bnd)
      omega
end Mpfx.Format
