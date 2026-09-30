-- Prove2me | solution 1 for lean_workbook_plus_57393
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T17:14:24.447873+00:00
-- url     : https://prove2.me/submissions/4bc27b92-8416-438d-93f0-84a2c311f7e2

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable def reciprocalPairLevel (a x : ℝ) : ℝ :=
  2*(x^2+a^2)/(x^2-a^2)^2

noncomputable def reciprocalPairOuterSquare (a k : ℝ) : ℝ :=
  (k*a^2+1+Real.sqrt (1+4*k*a^2))/k

noncomputable def reciprocalPairInnerSquare (a k : ℝ) : ℝ :=
  (k*a^2+1-Real.sqrt (1+4*k*a^2))/k

theorem reciprocalPair_cross (a k x : ℝ) (ha : 0 < a) (hk : 0 < k) :
    reciprocalPairLevel a x = k ↔ 2*(x^2+a^2) = k*(x^2-a^2)^2 := by
  constructor
  · intro h
    have hd : (x^2-a^2)^2 ≠ 0 := by
      intro hd
      unfold reciprocalPairLevel at h
      rw [hd,div_zero] at h
      exact hk.ne' h.symm
    exact (div_eq_iff hd).mp h
  · intro h
    have hd : (x^2-a^2)^2 ≠ 0 := by
      intro hd
      have hzero : x^2-a^2 = 0 := sq_eq_zero_iff.mp hd
      nlinarith [sq_pos_of_pos ha]
    exact (div_eq_iff hd).mpr h

theorem reciprocalPair_completed_square (a k x : ℝ) (ha : 0 < a) (hk : 0 < k) :
    reciprocalPairLevel a x = k ↔
      (k*(x^2-a^2)-1)^2 = 1+4*k*a^2 := by
  rw [reciprocalPair_cross a k x ha hk]
  have he : (k*(x^2-a^2)-1)^2-(1+4*k*a^2) =
      k*(k*(x^2-a^2)^2-2*(x^2+a^2)) := by ring
  constructor
  · intro h
    rw [← h] at he
    linarith only [he]
  · intro h
    have hz : k*(k*(x^2-a^2)^2-2*(x^2+a^2)) = 0 := by linarith only [he,h]
    have hz' := (mul_eq_zero.mp hz).resolve_left hk.ne'
    linarith only [hz']

theorem reciprocalPair_square_classification (a k x : ℝ) (ha : 0 < a) (hk : 0 < k) :
    reciprocalPairLevel a x = k ↔
      x^2 = reciprocalPairOuterSquare a k ∨ x^2 = reciprocalPairInnerSquare a k := by
  have hq : (Real.sqrt (1+4*k*a^2))^2 = 1+4*k*a^2 := Real.sq_sqrt (by positivity)
  rw [reciprocalPair_completed_square a k x ha hk,← hq,sq_eq_sq_iff_eq_or_eq_neg]
  unfold reciprocalPairOuterSquare reciprocalPairInnerSquare
  rw [eq_div_iff hk.ne',eq_div_iff hk.ne']
  constructor <;> intro h <;> rcases h with h | h
  · left; nlinarith only [h]
  · right; nlinarith only [h]
  · left; nlinarith only [h]
  · right; nlinarith only [h]

theorem reciprocalPair_outer_pos (a k : ℝ) (hk : 0 < k) :
    0 < reciprocalPairOuterSquare a k := by
  unfold reciprocalPairOuterSquare
  positivity

theorem reciprocalPair_inner_certificate (a k : ℝ) (hk : 0 < k) :
    reciprocalPairInnerSquare a k *
      (k*(k*a^2+1+Real.sqrt (1+4*k*a^2))) = k*a^2*(k*a^2-2) := by
  have hs := Real.sq_sqrt (show 0 ≤ 1+4*k*a^2 by positivity)
  unfold reciprocalPairInnerSquare
  calc
    _ = (k*a^2+1-Real.sqrt (1+4*k*a^2)) *
        (k*a^2+1+Real.sqrt (1+4*k*a^2)) := by field_simp
    _ = _ := by nlinarith only [hs]

theorem reciprocalPair_inner_nonneg_iff (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    0 ≤ reciprocalPairInnerSquare a k ↔ 2 ≤ k*a^2 := by
  have hb : 0 < k*(k*a^2+1+Real.sqrt (1+4*k*a^2)) := by positivity
  have hr : 0 < k*a^2 := by positivity
  have he := reciprocalPair_inner_certificate a k hk
  constructor
  · intro h
    have hh : 0 ≤ k*a^2*(k*a^2-2) := by rw [← he]; positivity
    have hh' : 0 ≤ k*a^2-2 := nonneg_of_mul_nonneg_right hh hr
    linarith only [hh']
  · intro h
    have hh : 0 ≤ reciprocalPairInnerSquare a k *
        (k*(k*a^2+1+Real.sqrt (1+4*k*a^2))) := by
      rw [he]
      exact mul_nonneg hr.le (sub_nonneg.mpr h)
    exact nonneg_of_mul_nonneg_left hh hb

theorem reciprocalPair_inner_zero_iff (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    reciprocalPairInnerSquare a k = 0 ↔ k*a^2 = 2 := by
  have hb : k*(k*a^2+1+Real.sqrt (1+4*k*a^2)) ≠ 0 := by positivity
  have hr : k*a^2 ≠ 0 := by positivity
  have he := reciprocalPair_inner_certificate a k hk
  constructor
  · intro h
    rw [h,zero_mul] at he
    have hh := (mul_eq_zero.mp he.symm).resolve_left hr
    linarith only [hh]
  · intro h
    have hz : k*a^2*(k*a^2-2) = 0 := by rw [h,sub_self,mul_zero]
    rw [hz] at he
    exact (mul_eq_zero.mp he).resolve_right hb

theorem reciprocalPair_inner_pos_iff (a k : ℝ) (ha : 0 < a) (hk : 0 < k) :
    0 < reciprocalPairInnerSquare a k ↔ 2 < k*a^2 := by
  constructor
  · intro h
    have hn : k*a^2 ≠ 2 := fun he => h.ne' ((reciprocalPair_inner_zero_iff a k ha hk).mpr he)
    exact lt_of_le_of_ne ((reciprocalPair_inner_nonneg_iff a k ha hk).mp h.le) hn.symm
  · intro h
    have hn : reciprocalPairInnerSquare a k ≠ 0 :=
      fun he => h.ne' ((reciprocalPair_inner_zero_iff a k ha hk).mp he)
    exact lt_of_le_of_ne ((reciprocalPair_inner_nonneg_iff a k ha hk).mpr h.le) hn.symm

theorem reciprocalPair_outer_gt_inner (a k : ℝ) (hk : 0 < k) :
    reciprocalPairInnerSquare a k < reciprocalPairOuterSquare a k := by
  unfold reciprocalPairInnerSquare reciprocalPairOuterSquare
  apply (div_lt_div_iff_of_pos_right hk).mpr
  have hs : 0 < Real.sqrt (1+4*k*a^2) := Real.sqrt_pos.mpr (by positivity)
  linarith only [hs]

theorem reciprocalPair_square_roots (u x : ℝ) (hu : 0 ≤ u) :
    x^2 = u ↔ x = Real.sqrt u ∨ x = -Real.sqrt u := by
  calc
    x^2 = u ↔ x^2 = (Real.sqrt u)^2 := by rw [Real.sq_sqrt hu]
    _ ↔ _ := sq_eq_sq_iff_eq_or_eq_neg

theorem reciprocalPair_two_roots (a k x : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hsmall : k*a^2 < 2) : reciprocalPairLevel a x = k ↔
      x = Real.sqrt (reciprocalPairOuterSquare a k) ∨
      x = -Real.sqrt (reciprocalPairOuterSquare a k) := by
  rw [reciprocalPair_square_classification a k x ha hk]
  have hn : ¬ 0 ≤ reciprocalPairInnerSquare a k := by
    rw [reciprocalPair_inner_nonneg_iff a k ha hk]
    exact not_le.mpr hsmall
  have hne : x^2 ≠ reciprocalPairInnerSquare a k := by
    intro h
    exact hn (h ▸ sq_nonneg x)
  rw [or_iff_left hne]
  exact reciprocalPair_square_roots _ x (reciprocalPair_outer_pos a k hk).le

theorem reciprocalPair_three_roots (a k x : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hcritical : k*a^2 = 2) : reciprocalPairLevel a x = k ↔
      x = Real.sqrt (reciprocalPairOuterSquare a k) ∨
      x = -Real.sqrt (reciprocalPairOuterSquare a k) ∨ x = 0 := by
  rw [reciprocalPair_square_classification a k x ha hk,
    (reciprocalPair_inner_zero_iff a k ha hk).mpr hcritical,sq_eq_zero_iff,
    reciprocalPair_square_roots _ x (reciprocalPair_outer_pos a k hk).le,or_assoc]

theorem reciprocalPair_four_roots (a k x : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hlarge : 2 < k*a^2) : reciprocalPairLevel a x = k ↔
      x = Real.sqrt (reciprocalPairOuterSquare a k) ∨
      x = -Real.sqrt (reciprocalPairOuterSquare a k) ∨
      x = Real.sqrt (reciprocalPairInnerSquare a k) ∨
      x = -Real.sqrt (reciprocalPairInnerSquare a k) := by
  rw [reciprocalPair_square_classification a k x ha hk,
    reciprocalPair_square_roots _ x (reciprocalPair_outer_pos a k hk).le,
    reciprocalPair_square_roots _ x ((reciprocalPair_inner_pos_iff a k ha hk).mpr hlarge).le,
    or_assoc]

theorem reciprocalPair_roots_distinct (a k : ℝ) (ha : 0 < a) (hk : 0 < k)
    (hlarge : 2 < k*a^2) :
    0 < Real.sqrt (reciprocalPairInnerSquare a k) ∧
      Real.sqrt (reciprocalPairInnerSquare a k) < Real.sqrt (reciprocalPairOuterSquare a k) := by
  have hi := (reciprocalPair_inner_pos_iff a k ha hk).mpr hlarge
  exact ⟨Real.sqrt_pos.mpr hi,Real.sqrt_lt_sqrt hi.le (reciprocalPair_outer_gt_inner a k hk)⟩

theorem reciprocalPair_partial_fractions (a x : ℝ) (h : x^2 ≠ a^2) :
    1/(x-a)^2+1/(x+a)^2 = reciprocalPairLevel a x := by
  have hm : x-a ≠ 0 := fun hm => h (congrArg (fun t : ℝ => t^2) (sub_eq_zero.mp hm))
  have hp : x+a ≠ 0 := by
    intro hp
    apply h
    have hx : x = -a := by linarith only [hp]
    rw [hx,neg_sq]
  have hd : x^2-a^2 ≠ 0 := sub_ne_zero.mpr h
  unfold reciprocalPairLevel
  field_simp
  ring

theorem reciprocalPair_normalized_roots (x : ℝ) :
    2*(x^2+1/4)/(x^2-1/4)^2 = (13:ℝ)/36 ↔ x = 5/2 ∨ x = -5/2 := by
  constructor
  · intro h
    have hd : (x^2-1/4)^2 ≠ 0 := by
      intro hd
      rw [hd,div_zero] at h
      norm_num at h
    have hc := (div_eq_iff hd).mp h
    have he : (4*x^2-25)*(52*x^2+11) = 0 := by nlinarith only [hc]
    have hp : 52*x^2+11 ≠ 0 := by positivity
    have hz := (mul_eq_zero.mp he).resolve_right hp
    have hl : (2*x-5)*(2*x+5) = 0 := by nlinarith only [hz]
    rcases mul_eq_zero.mp hl with h | h
    · left; linarith only [h]
    · right; linarith only [h]
  · rintro (rfl | rfl) <;> norm_num

theorem reciprocalPair_shifted_roots (x : ℝ) :
    2*((x+59/2)^2+1/4)/((x+59/2)^2-1/4)^2 = (13:ℝ)/36 ↔
      x = -27 ∨ x = -32 := by
  rw [reciprocalPair_normalized_roots]
  constructor <;> intro h <;> rcases h with h | h
  · left; linarith only [h]
  · right; linarith only [h]
  · left; linarith only [h]
  · right; linarith only [h]

theorem reciprocalPair_shifted_partial_fractions (x : ℝ) (h29 : x ≠ -29) (h30 : x ≠ -30) :
    1/(x+30)^2+1/(x+29)^2 =
      2*((x+59/2)^2+1/4)/((x+59/2)^2-1/4)^2 := by
  have hd : (x+59/2)^2 ≠ (1/2:ℝ)^2 := by
    intro hd
    have hm : (x+30)*(x+29) = 0 := by nlinarith only [hd]
    rcases mul_eq_zero.mp hm with hm | hm
    · apply h30; linarith only [hm]
    · apply h29; linarith only [hm]
  have hi := reciprocalPair_partial_fractions (1/2) (x+59/2) hd
  unfold reciprocalPairLevel at hi
  have hm : x+59/2-1/2 = x+29 := by ring
  have hp : x+59/2+1/2 = x+30 := by ring
  have ha : (1/2:ℝ)^2 = 1/4 := by ring
  rw [hm,hp,ha] at hi
  calc
    _ = 1/(x+29)^2+1/(x+30)^2 := add_comm _ _
    _ = _ := hi

theorem reciprocalPair_source_roots (x : ℝ) :
    1/(x+30)^2+1/(x+29)^2 = (13:ℝ)/36 ↔ x = -27 ∨ x = -32 := by
  by_cases h29 : x = -29
  · subst x
    norm_num
    change (1:ℝ)+0 ≠ 13/36
    norm_num
  by_cases h30 : x = -30
  · subst x
    norm_num
    change (0:ℝ)+1 ≠ 13/36
    norm_num
  rw [reciprocalPair_shifted_partial_fractions x h29 h30,reciprocalPair_shifted_roots]

theorem solution : ¬ (∀ x : ℝ,
    2*(x^2+1/4)/(x^2-1/4)^2 = (13:ℝ)/36 → x = -3 ∨ x = 2) := by
  intro h
  have hx := h (5/2) ((reciprocalPair_normalized_roots (5/2)).mpr (Or.inl rfl))
  rcases hx with hx | hx <;> norm_num at hx

#print axioms reciprocalPairLevel
#print axioms reciprocalPairOuterSquare
#print axioms reciprocalPairInnerSquare
#print axioms reciprocalPair_cross
#print axioms reciprocalPair_completed_square
#print axioms reciprocalPair_square_classification
#print axioms reciprocalPair_outer_pos
#print axioms reciprocalPair_inner_certificate
#print axioms reciprocalPair_inner_nonneg_iff
#print axioms reciprocalPair_inner_zero_iff
#print axioms reciprocalPair_inner_pos_iff
#print axioms reciprocalPair_outer_gt_inner
#print axioms reciprocalPair_square_roots
#print axioms reciprocalPair_two_roots
#print axioms reciprocalPair_three_roots
#print axioms reciprocalPair_four_roots
#print axioms reciprocalPair_roots_distinct
#print axioms reciprocalPair_partial_fractions
#print axioms reciprocalPair_normalized_roots
#print axioms reciprocalPair_shifted_roots
#print axioms reciprocalPair_shifted_partial_fractions
#print axioms reciprocalPair_source_roots
#print axioms solution
