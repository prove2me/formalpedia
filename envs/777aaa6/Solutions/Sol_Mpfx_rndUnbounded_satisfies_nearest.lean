-- Prove2me | solution 1 for Mpfx.rndUnbounded_satisfies_nearest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:25:26.791744+00:00
-- url     : https://prove2.me/submissions/0bf07d69-709e-4762-9907-9acdef2f5dc3

import Definitions.Def_Mpfx_Rounding_Op_Defs
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
import Definitions.Def_Mpfx_Rounding_Op_Nearest
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_RoundsFinite_nearest_awayZero_of_bracket
import Theorems.Thm_Mpfx_RoundsFinite_nearest_toEven_of_bracket
import Theorems.Thm_Mpfx_RoundsFinite_self
import Theorems.Thm_Mpfx_RoundsFinite_toNegative_floor
import Theorems.Thm_Mpfx_RoundsFinite_toPositive_floor_add_one
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_neighbors_alternate
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow



set_option autoImplicit true
open Mpfx
attribute [local instance] Classical.propDecidable
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (tb : TieBreak) (x : ℝ)
    (h : ¬ F.IsUndefined (.nearest tb)) :
    RoundsFinite F.unbounded (.nearest tb) x (rndUnbounded F (.nearest tb) x h) := by
  set e := F.canonicalExp x
  set s := x * (2 : ℝ) ^ (-e)
  set lo := ⌊s⌋
  set dlo := Dyadic.ofIntZpow lo e
  set dhi := Dyadic.ofIntZpow (lo + 1) e
  have hd : RoundsFinite F.unbounded .toNegative x dlo := RoundsFinite.toNegative_floor F x
  have h2e : (0 : ℝ) < 2 ^ e := zpow_pos two_pos e
  have hs_eq : s * 2 ^ e = x := mul_zpow_neg_self x e
  have hlo := Int.floor_le s
  by_cases hs : (lo : ℝ) = s
  · -- The fraction is `0`: both modes take the floor point, and it is `x`.
    have hδ : s - lo < 1 / 2 := by rw [← hs, sub_self]; norm_num
    have hval : rndUnbounded F (.nearest tb) x h = dlo := by
      cases tb <;> exact congrArg (Dyadic.ofIntZpow · e) (if_pos hδ)
    have hx : x = (dlo : ℝ) := by rw [Dyadic.coe_ofIntZpow, hs, hs_eq]
    have := RoundsFinite.self (F := F.unbounded) (.nearest tb) hd.1
    rw [hval]
    rwa [← hx] at this
  have hu : RoundsFinite F.unbounded .toPositive x dhi := RoundsFinite.toPositive_floor_add_one F hs
  -- Distances to the two neighbours, in units of the step.
  have hdlo : |x - (dlo : ℝ)| = (s - lo) * 2 ^ e := by
    rw [abs_of_nonneg (by linarith [hd.2.1]), Dyadic.coe_ofIntZpow, ← hs_eq]; ring
  have hdhi : |x - (dhi : ℝ)| = (1 - (s - lo)) * 2 ^ e := by
    rw [abs_of_nonpos (by linarith [hu.2.1]), Dyadic.coe_ofIntZpow, ← hs_eq]; push_cast; ring
  have hlt : s - lo < 1 / 2 → |x - (dlo : ℝ)| < |x - (dhi : ℝ)| := fun hδ => by
    rw [hdlo, hdhi]; exact mul_lt_mul_of_pos_right (by linarith) h2e
  have hgt : 1 / 2 < s - lo → |x - (dhi : ℝ)| < |x - (dlo : ℝ)| := fun hδ => by
    rw [hdlo, hdhi]; exact mul_lt_mul_of_pos_right (by linarith) h2e
  have htie : ¬ s - lo < 1 / 2 → ¬ 1 / 2 < s - lo → |x - (dlo : ℝ)| = |x - (dhi : ℝ)| :=
    fun h₁ h₂ => by rw [hdlo, hdhi]; congr 1; linarith
  -- On a tie `x` is the midpoint: `dlo + dhi = 2x`.
  have hmid : ¬ s - lo < 1 / 2 → ¬ 1 / 2 < s - lo → (dlo : ℝ) + dhi = 2 * x := fun h₁ h₂ => by
    have := htie h₁ h₂
    rw [abs_of_nonneg (by linarith [hd.2.1]), abs_of_nonpos (by linarith [hu.2.1])] at this
    linarith
  cases tb with
  | awayZero =>
    change RoundsFinite _ _ x (Dyadic.ofIntZpow (if s - lo < 1 / 2 then lo
      else if 1 / 2 < s - lo then lo + 1 else if 0 ≤ x then lo + 1 else lo) e)
    split_ifs with h₁ h₂ hx
    · exact RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (hlt h₁).le⟩ fun h _ => absurd h (hlt h₁).ne
    · exact RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inr rfl)
        ⟨(hgt h₂).le, le_rfl⟩ fun h _ => absurd h.symm (hgt h₂).ne
    · refine RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inr rfl)
        ⟨(htie h₁ h₂).ge, le_rfl⟩ fun _ _ => ⟨?_, le_rfl⟩
      rw [abs_of_nonneg (hx.trans hu.2.1), abs_le]
      constructor <;> linarith [hmid h₁ h₂, hd.2.1, hu.2.1]
    · refine RoundsFinite.nearest_awayZero_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (htie h₁ h₂).le⟩ fun _ _ => ⟨le_rfl, ?_⟩
      push Not at hx
      rw [abs_of_neg (hd.2.1.trans_lt hx), abs_le]
      constructor <;> linarith [hmid h₁ h₂, hd.2.1, hu.2.1]
  | toEven =>
    have hodd : ¬ F.IsUndefined .toOdd := fun ⟨h₁, h₂, _⟩ => h ⟨h₁, h₂, Or.inr rfl⟩
    change RoundsFinite _ _ x (Dyadic.ofIntZpow (if s - lo < 1 / 2 then lo
      else if 1 / 2 < s - lo then lo + 1 else if F.IsEven dlo then lo else lo + 1) e)
    split_ifs with h₁ h₂ hev
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (hlt h₁).le⟩ fun h _ => absurd h (hlt h₁).ne
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inr rfl)
        ⟨(hgt h₂).le, le_rfl⟩ fun h _ => absurd h.symm (hgt h₂).ne
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inl rfl)
        ⟨le_rfl, (htie h₁ h₂).le⟩ fun _ _ => hev
    · exact RoundsFinite.nearest_toEven_of_bracket hd hu (Or.inr rfl)
        ⟨(htie h₁ h₂).ge, le_rfl⟩ fun _ _ =>
          ⟨hu.1, fun ho => hev ⟨hd.1, (neighbors_alternate x hodd hs).mp ho⟩⟩
end Mpfx
