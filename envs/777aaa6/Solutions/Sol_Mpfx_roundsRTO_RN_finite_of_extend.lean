-- Prove2me | solution 1 for Mpfx.roundsRTO_RN_finite_of_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:22:54.265183+00:00
-- url     : https://prove2.me/submissions/aeb2722b-bdc9-4000-a7e9-960f47435868

import Definitions.Def_Mpfx_DoubleRounding_Basic
import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Theorems.Thm_Mpfx_Dyadic_coe_midpoint
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_midpoint_comm
import Theorems.Thm_Mpfx_Format_extend_mono
import Theorems.Thm_Mpfx_Format_extend_one_extend_one_subset_extend_two
import Theorems.Thm_Mpfx_Format_self_subset_extend
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_IsFaithfulRound_iff_of_between
import Theorems.Thm_Mpfx_IsFaithfulRound_opposite_sides_of_ne
import Theorems.Thm_Mpfx_IsFaithfulRound_same_side
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_RoundsFinite_nearest_min
import Theorems.Thm_Mpfx_toOdd_notMem_of_extend_subset
import Theorems.Thm_P2M_Mpfx_midpoint_in_F__extend_one_of_F_adjacent_ade54236b524

section
namespace Mpfx
private theorem midpoint_mem_extend_one_of_faithful {F : FiniteFormat} {x : ℝ} {a b : Dyadic}
    (ha : IsFaithfulRound F x a) (hb : IsFaithfulRound F x b) (hab : a ≠ b) :
    Dyadic.midpoint a b ∈ F.extend 1 := by
  have key : ∀ {d u : Dyadic}, RoundsFinite F .toNegative x d →
      RoundsFinite F .toPositive x u → d ≠ u → Dyadic.midpoint d u ∈ F.extend 1 :=
    fun {d u} hd hu hdu => midpoint_in_F₁_extend_one_of_F_adjacent hd.1 hu.1
      (lt_of_le_of_ne (hd.2.1.trans hu.2.1) fun h => hdu (Dyadic.ext_real h))
      fun y hy hdy => hu.2.2 y hy
        (not_le.mp fun hyx => absurd (hd.2.2 y hy hyx) (not_le.mpr hdy)).le
  rcases ha.opposite_sides_of_ne hb hab with ⟨hd, hu⟩ | ⟨hd, hu⟩
  · exact key hd hu hab
  · rw [Dyadic.midpoint_comm]; exact key hd hu hab.symm
private theorem closer_of_same_side {x z a b : ℝ} (hab : a ≠ b)
    (hz : |z - a| ≤ |z - b|) (hzm : z ≠ (a + b) / 2)
    (hside : 0 < (x - (a + b) / 2) * (z - (a + b) / 2)) : |x - a| < |x - b| := by
  rw [← sq_lt_sq]
  have h1 := sq_le_sq.mpr hz
  have hzm' : z - (a + b) / 2 ≠ 0 := sub_ne_zero.mpr hzm
  have hP : (b - a) * (z - (a + b) / 2) < 0 :=
    lt_of_le_of_ne (by nlinarith [h1]) (mul_ne_zero (sub_ne_zero.mpr hab.symm) hzm')
  have hz2 : 0 < (z - (a + b) / 2) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hzm'))
  have hQ : (b - a) * (x - (a + b) / 2) < 0 := by
    have := mul_neg_of_neg_of_pos hP hside
    nlinarith
  nlinarith [hQ]
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub2 : (F₁.extend 2).toFormat ⊆ F₂.toFormat)
    (hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p)
    {tb : TieBreak} {x : ℝ} {z w' : Dyadic}
    (hz : RoundsFinite F₂ .toOdd x z)
    (hw : RoundsFinite F₁ (.nearest tb) (z : ℝ) w') :
    RoundsFinite F₁ (.nearest tb) x w' := by
  have hsub_ext1 : (F₁.extend 1).toFormat ⊆ F₂.toFormat :=
    (Format.extend_mono F₁.toFormat (by norm_num)).trans hsub2
  have hsub' : F₁.toFormat ⊆ F₂.toFormat := (Format.self_subset_extend _ 1).trans hsub_ext1
  rcases eq_or_ne ((z : ℝ)) x with hzx | hzx
  · rw [hzx] at hw; exact hw
  have hxne : x ≠ (z : ℝ) := fun h => hzx h.symm
  have hsub_double : ((F₁.extend 1).extend 1).toFormat ⊆ F₂.toFormat :=
    (Format.extend_one_extend_one_subset_extend_two _).trans hsub2
  have hz_ext1 : z ∉ F₁.extend 1 := toOdd_notMem_of_extend_subset hsub_double hp_F₂ hz hxne
  have hz₁ : z ∉ F₁ := fun h => hz_ext1 (Format.self_subset_extend _ 1 z h)
  have hiff := IsFaithfulRound.iff_of_between hsub' hz.2.1 hz₁
  have hwf : IsFaithfulRound F₁ x w' := (hiff w').mpr hw.isFaithfulRound
  -- Every other faithful rounding of `x` is strictly farther than `w'`.
  have hcloser : ∀ c : Dyadic, c ∈ F₁ → IsFaithfulRound F₁ x c → c ≠ w' →
      |x - (w' : ℝ)| < |x - (c : ℝ)| := fun c hc hcf hcw => by
    have hm₁ := midpoint_mem_extend_one_of_faithful hwf hcf hcw.symm
    have hm₂ : Dyadic.midpoint w' c ∈ F₂ := hsub_ext1 _ hm₁
    have hzm : (z : ℝ) ≠ Dyadic.midpoint w' c := fun h => hz_ext1 (Dyadic.ext_real h ▸ hm₁)
    have hxm : x ≠ Dyadic.midpoint w' c := fun h => by
      have hzm' : z = Dyadic.midpoint w' c :=
        RoundsFinite.eq_of_mem hm₂ (by rw [← h]; exact hz)
      exact hxne (by rw [h, hzm'])
    have hside := hz.2.1.same_side hm₂ hxm hzm
    rw [Dyadic.coe_midpoint] at hzm hside
    exact closer_of_same_side (fun h => hcw (Dyadic.ext_real h).symm)
      (hw.nearest_min hc ((hiff c).mp hcf)) hzm hside
  have hclose : ∀ c : Dyadic, c ∈ F₁ → IsFaithfulRound F₁ x c →
      |x - (w' : ℝ)| ≤ |x - (c : ℝ)| := fun c hc hcf => by
    rcases eq_or_ne c w' with rfl | hcw
    · exact le_rfl
    · exact (hcloser c hc hcf hcw).le
  cases tb with
  | toEven => exact ⟨hw.1, hwf, hclose, fun ⟨c, hc, hcf, hcw, h⟩ =>
      absurd h (hcloser c hc hcf hcw).ne⟩
  | awayZero => exact ⟨hw.1, hwf, hclose, fun c hc hcf hcw h =>
      absurd h (hcloser c hc hcf hcw).ne⟩
end Mpfx
