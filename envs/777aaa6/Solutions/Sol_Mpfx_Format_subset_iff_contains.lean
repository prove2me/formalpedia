-- Prove2me | solution 1 for Mpfx.Format.subset_iff_contains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:09.894927+00:00
-- url     : https://prove2.me/submissions/a09490ae-55d8-45a0-b7d8-4ce17edbc5f2

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_containsPrec
import Theorems.Thm_Mpfx_Format_containsSub
import Theorems.Thm_Mpfx_Format_b_top_of_subset
import Theorems.Thm_Mpfx_Format_exp_le_of_subset
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_not_precisionAtMost_of_odd
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_coe
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_zero_iff_eq_zero
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_Format_Nontrivial_p_ne_zero
import Theorems.Thm_Mpfx_Format_bound_mem
import Theorems.Thm_Mpfx_Format_ofIntZpow_mem
import Theorems.Thm_Mpfx_NonNegDyadic_le_iff_coe_real
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_nonneg_coe_real
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow


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
private theorem b_le_of_subset {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial)
    (h : F₁ ⊆ F₂) : F₁.b ≤ F₂.b := by
  cases hb2 : F₂.b using Bound.recTopCoe with
  | top => exact le_top
  | coe b₂ =>
    cases hb1 : F₁.b using Bound.recTopCoe with
    | coe b₁ =>
      refine WithTop.coe_le_coe.mpr (NonNegDyadic.le_iff_coe_real.mpr ?_)
      have := (h _ (bound_mem hbr hb1)).2.2
      rw [hb2] at this
      rw [← abs_of_nonneg (a := ((b₁.val : Dyadic) : ℝ)) (nonneg_coe_real b₁)]
      exact abs_coe_real_le_of_boundOK this
    | top =>
      exact absurd (b_top_of_subset hnt.p_ne_zero hb1 h) (by rw [hb2]; exact WithTop.coe_ne_top)
private theorem wit_pos (p : ℕ) : 0 < wit p := by unfold wit; positivity
private theorem odd_wit {p : ℕ} (hp : 0 < p) : Odd (wit p) :=
  (by rw [Int.even_pow]; exact ⟨even_two, hp.ne'⟩ : Even ((2 : ℤ) ^ p)).add_one
private theorem not_precisionAtMost_wit {p₂ : ℕ} (hp : 0 < p₂) (k : ℤ) :
    ¬ Dyadic.precisionAtMost (p₂ : Prec) (Dyadic.ofIntZpow (wit p₂) k) :=
  Dyadic.not_precisionAtMost_of_odd (odd_wit hp) (by rw [Dyadic.coe_ofIntZpow])
    (by rw [abs_of_pos (wit_pos p₂)]; unfold wit; omega)
private theorem precisionAtMost_wit {p₁ : Prec} {p₂ : ℕ} (hp : 0 < p₂)
    (hlt : (p₂ : Prec) < p₁) (k : ℤ) :
    Dyadic.precisionAtMost p₁ (Dyadic.ofIntZpow (wit p₂) k) := by
  cases hp' : p₁ using ENat.recTopCoe with
  | top => trivial
  | coe q =>
    rw [Dyadic.precisionAtMost_coe]
    refine ⟨wit p₂, k, by rw [Dyadic.coe_rat_ofIntZpow], ?_⟩
    have hq : p₂ + 1 ≤ q := by
      have : (p₂ : Prec) < (q : Prec) := hp' ▸ hlt
      exact Nat.succ_le_of_lt (ENat.coe_lt_coe.mp this)
    have h1 : (1 : ℤ) < 2 ^ p₂ := one_lt_pow₀ (by norm_num) hp.ne'
    calc |wit p₂| = 2 ^ p₂ + 1 := by rw [abs_of_pos (wit_pos p₂)]; rfl
      _ < 2 ^ (p₂ + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hq
private theorem abs_coe_wit (p₂ : ℕ) (k : ℤ) :
    |((Dyadic.ofIntZpow (wit p₂) k : Dyadic) : ℝ)| = ((wit p₂ : ℤ) : ℝ) * (2 : ℝ) ^ k := by
  have hw : (0 : ℝ) < ((wit p₂ : ℤ) : ℝ) := by exact_mod_cast wit_pos p₂
  rw [Dyadic.coe_ofIntZpow, abs_of_pos (mul_pos hw (zpow_pos (by norm_num) k))]
private theorem sub_test_of_subset {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial)
    (h : F₁ ⊆ F₂) (hp : ¬ F₁.p ≤ F₂.p) :
    ∃ (e₁ : ℤ) (p₂ : ℕ), F₁.exp = (e₁ : QExp) ∧ 0 < p₂ ∧ F₂.p = (p₂ : Prec) ∧
      F₁.b ≤ ((nnPow (e₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound) := by
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hnt
  have hlt : F₂.p < F₁.p := lt_of_not_ge hp
  cases hp2 : F₂.p using ENat.recTopCoe with
  | top => exact absurd (hp2 ▸ hlt) (not_lt_of_ge le_top)
  | coe p₂ =>
  rcases Nat.eq_zero_or_pos p₂ with rfl | hp₂pos
  · -- `p₂ = 0`: `F₂` holds only `0`, contradicting `F₁`'s nonzero member.
    exfalso
    have hx₀p := (h _ hx₀).1
    rw [hp2] at hx₀p
    exact hx₀ne (Dyadic.precisionAtMost_zero_iff_eq_zero.mp hx₀p)
  have hwpos : (0 : ℝ) < ((wit p₂ : ℤ) : ℝ) := by exact_mod_cast wit_pos p₂
  -- The witness is never in `F₂`, so it must fail `F₁`'s quantum or bound check.
  have key : ∀ k : ℤ, F₁.exp ≤ (k : QExp) →
      boundOK F₁.b (Dyadic.ofIntZpow (wit p₂) k) → False := by
    intro k hk hbk
    have hmem := (h _ (ofIntZpow_mem (precisionAtMost_wit hp₂pos (hp2 ▸ hlt) k) hk hbk)).1
    rw [hp2] at hmem
    exact not_precisionAtMost_wit hp₂pos k hmem
  cases he1 : F₁.exp using QExp.recBotCoe with
  | bot =>
    -- `exp₁ = -∞`: the witness can be scaled below any positive bound.
    exfalso
    obtain ⟨k, hk⟩ : ∃ k : ℤ, boundOK F₁.b (Dyadic.ofIntZpow (wit p₂) k) := by
      cases hb1 : F₁.b using Bound.recTopCoe with
      | top => exact ⟨0, trivial⟩
      | coe b₁ =>
        have hpos : 0 < ((b₁.val : Dyadic) : ℝ) :=
          lt_of_lt_of_le (abs_pos.mpr (by exact_mod_cast hx₀ne))
              (abs_coe_real_le_of_boundOK (hb1 ▸ hx₀.2.2))
        obtain ⟨k, -, hk⟩ := exists_mul_zpow_le hwpos hpos 0
        exact ⟨k, boundOK_coe_of_abs_le (by rw [abs_coe_wit]; exact hk)⟩
    exact key k (by rw [he1]; exact bot_le) hk
  | coe e₁ =>
    refine ⟨e₁, p₂, rfl, hp₂pos, rfl, ?_⟩
    cases hb1 : F₁.b using Bound.recTopCoe with
    | top => exact absurd (key e₁ (by rw [he1]) (by rw [hb1]; trivial)) not_false
    | coe b₁ =>
      -- `b₁` is a value of `F₁`, `b₁ = m · 2^exp₁`; if `b₁ > 2^(exp₁+p₂)` then
      -- `m ≥ wit p₂`, so the witness is in bound.
      refine WithTop.coe_le_coe.mpr (NonNegDyadic.le_iff_coe_real.mpr ?_)
      by_contra hcon
      have h2e : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
      rw [coe_real_nnPow] at hcon
      push Not at hcon
      obtain ⟨m, hm⟩ : ∃ m : ℤ, ((b₁.val : Dyadic) : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ := by
        rw [← Dyadic.quantumAtLeast_coe_real]
        exact he1 ▸ (hbr b₁ hb1).2.1
      have hm_ge : ((wit p₂ : ℤ) : ℝ) ≤ (m : ℝ) := by
        have h1 : (2 : ℝ) ^ p₂ < (m : ℝ) := by
          refine lt_of_mul_lt_mul_right ?_ (le_of_lt h2e)
          rw [hm, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast,
            mul_comm ((2 : ℝ) ^ e₁)] at hcon
          exact hcon
        have h2 : (2 : ℤ) ^ p₂ < m := by exact_mod_cast h1
        exact_mod_cast (by unfold wit; omega : wit p₂ ≤ m)
      refine key e₁ (by rw [he1]) (hb1 ▸ boundOK_coe_of_abs_le ?_)
      rw [abs_coe_wit, hm]
      exact mul_le_mul_of_nonneg_right hm_ge (le_of_lt h2e)
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
theorem _root_.solution {F₁ F₂ : Format} (hbr : BoundRep F₁) (hnt : F₁.Nontrivial) :
    F₁ ⊆ F₂ ↔ ContainsPrec F₁ F₂ ∨ ContainsSub F₁ F₂ := by
  constructor
  · intro h
    have hb := b_le_of_subset hbr hnt h
    have he := exp_le_of_subset hnt h
    by_cases hp : F₁.p ≤ F₂.p
    · exact Or.inl ⟨hp, he, hb, h.specials⟩
    · obtain ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb⟩ := sub_test_of_subset hbr hnt h hp
      exact Or.inr ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb, he, hb, h.specials⟩
  · rintro (⟨hp, he, hb, hs⟩ | ⟨e₁, p₂, he₁, hp₂pos, hp₂, hbb, he, hb, hs⟩)
    · exact containsPrec hp he hb hs
    · exact containsSub he₁ hp₂pos hp₂ hbb he hb hs
end Mpfx.Format
