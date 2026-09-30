-- Prove2me | solution 1 for lean_workbook_plus_79336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:16:55.937037+00:00
-- url     : https://prove2.me/submissions/006cd380-f6b7-4825-8158-07734ae985ac

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private def reciprocalFactor (a : ℤ) : ℚ := 1 + 1 / (a : ℚ)

private theorem reciprocal_factor_upper (a k : ℤ) (hk : 0 < k) (ha : k ≤ a) :
    reciprocalFactor a ≤ 1 + 1 / (k : ℚ) := by
  unfold reciprocalFactor
  simpa only [add_comm] using add_le_add_left (one_div_le_one_div_of_le (a := (k : ℚ)) (b := (a : ℚ))
    (by exact_mod_cast hk) (by exact_mod_cast ha)) (1 : ℚ)

private theorem reciprocal_factor_bounds (a : ℤ) (ha : a ≠ 0) :
    0 ≤ reciprocalFactor a ∧ reciprocalFactor a ≤ 2 := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have haq : (a : ℚ) < 0 := by exact_mod_cast hneg
    have ha1 : (a : ℚ) ≤ -1 := by exact_mod_cast (show a ≤ -1 by omega)
    have hlo : (-1 : ℚ) ≤ 1 / (a : ℚ) :=
      (le_div_iff_of_neg haq).mpr (by linarith)
    have hhi : 1 / (a : ℚ) < 0 := div_neg_of_pos_of_neg (by norm_num) haq
    dsimp [reciprocalFactor]
    constructor <;> linarith
  · have haq : (0 : ℚ) < a := by exact_mod_cast hpos
    have hlo := div_pos (show (0 : ℚ) < 1 by norm_num) haq
    have hhi := reciprocal_factor_upper a 1 (by norm_num) (by omega)
    norm_num at hhi
    exact ⟨by dsimp [reciprocalFactor]; linarith, hhi⟩

private theorem reciprocal_factor_not_one (a : ℤ) (ha : a ≠ 0) (h1 : a ≠ 1) :
    reciprocalFactor a ≤ 3 / 2 := by
  by_cases hp : 0 < a
  · have h := reciprocal_factor_upper a 2 (by norm_num) (by omega)
    norm_num at h
    exact h
  · have hn : (a : ℚ) < 0 := by exact_mod_cast (show a < 0 by omega)
    have hh : 1 / (a : ℚ) < 0 := div_neg_of_pos_of_neg (by norm_num) hn
    dsimp [reciprocalFactor]
    linarith

private theorem reciprocal_product_negative (a b c : ℤ)
    (ha : a < 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c = 3) :
    a = -4 ∧ b = 1 ∧ c = 1 := by
  obtain ⟨ha0, _⟩ := reciprocal_factor_bounds a (by omega)
  obtain ⟨hb0, hb2⟩ := reciprocal_factor_bounds b hb
  obtain ⟨hc0, hc2⟩ := reciprocal_factor_bounds c hc
  have han : reciprocalFactor a < 1 := by
    have haq : (a : ℚ) < 0 := by exact_mod_cast ha
    have hh : 1 / (a : ℚ) < 0 := div_neg_of_pos_of_neg (by norm_num) haq
    dsimp [reciprocalFactor]
    linarith
  have hb1 : b = 1 := by
    by_contra hn
    have hb3 := reciprocal_factor_not_one b hb hn
    have hh : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c ≤
        reciprocalFactor a * (3 / 2) * 2 := by gcongr
    nlinarith
  have hc1 : c = 1 := by
    by_contra hn
    have hc3 := reciprocal_factor_not_one c hc hn
    have hh : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c ≤
        reciprocalFactor a * 2 * (3 / 2) := by gcongr
    nlinarith
  subst b
  subst c
  norm_num [reciprocalFactor] at h
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  field_simp [haq] at h
  have har : (a : ℚ) = -4 := by linarith
  exact ⟨by exact_mod_cast har, rfl, rfl⟩

private theorem reciprocal_product_sorted (a b c : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≤ b) (hbc : b ≤ c)
    (h : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c = 3) :
    (a = -4 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 3 ∧ c = 8) ∨
      (a = 1 ∧ b = 4 ∧ c = 5) ∨ (a = 2 ∧ b = 2 ∧ c = 3) := by
  by_cases hn : a < 0
  · exact Or.inl (reciprocal_product_negative a b c hn hb hc h)
  have ha1 : 1 ≤ a := by omega
  obtain ⟨ha0, ha2⟩ := reciprocal_factor_bounds a ha
  obtain ⟨hb0, _⟩ := reciprocal_factor_bounds b hb
  obtain ⟨hc0, _⟩ := reciprocal_factor_bounds c hc
  have ha_le : a ≤ 2 := by
    by_contra hn
    have hfa := reciprocal_factor_upper a 3 (by norm_num) (by omega)
    have hfb := reciprocal_factor_upper b 3 (by norm_num) (by omega)
    have hfc := reciprocal_factor_upper c 3 (by norm_num) (by omega)
    norm_num at hfa hfb hfc
    have hh : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c ≤
        (4 / 3 : ℚ) * (4 / 3) * (4 / 3) := by gcongr
    norm_num at hh
    linarith
  have hb_le : b ≤ 4 := by
    by_contra hn
    have hfb := reciprocal_factor_upper b 5 (by norm_num) (by omega)
    have hfc := reciprocal_factor_upper c 5 (by norm_num) (by omega)
    norm_num at hfb hfc
    have hh : reciprocalFactor a * reciprocalFactor b * reciprocalFactor c ≤
        (2 : ℚ) * (6 / 5) * (6 / 5) := by gcongr
    norm_num at hh
    linarith
  have hb1 : 1 ≤ b := by omega
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  dsimp [reciprocalFactor] at h
  field_simp [haq, hbq, hcq] at h
  have hi : (a + 1) * (b + 1) * (c + 1) = a * b * c * 3 := by
    exact_mod_cast h
  interval_cases a <;> interval_cases b <;> norm_num at hi ⊢ <;> omega

def reciprocalProductTriples : Finset (ℤ × ℤ × ℤ) :=
  {(-4, 1, 1), (1, -4, 1), (1, 1, -4),
   (1, 3, 8), (1, 8, 3), (3, 1, 8), (3, 8, 1), (8, 1, 3), (8, 3, 1),
   (1, 4, 5), (1, 5, 4), (4, 1, 5), (4, 5, 1), (5, 1, 4), (5, 4, 1),
   (2, 2, 3), (2, 3, 2), (3, 2, 2)}

theorem rational_reciprocal_product_classification (a b c : ℤ) :
    (a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧
      (1 + 1 / (a : ℚ)) * (1 + 1 / (b : ℚ)) * (1 + 1 / (c : ℚ)) = 3) ↔
      (a, b, c) ∈ reciprocalProductTriples := by
  constructor
  · rintro ⟨ha, hb, hc, h⟩
    change reciprocalFactor a * reciprocalFactor b * reciprocalFactor c = 3 at h
    rcases le_total a b with hab | hba
    · rcases le_total b c with hbc | hcb
      · rcases reciprocal_product_sorted a b c ha hb hc hab hbc h with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
          decide
      · rcases le_total a c with hac | hca
        · have h' : reciprocalFactor a * reciprocalFactor c * reciprocalFactor b = 3 := by
            nlinarith [h]
          rcases reciprocal_product_sorted a c b ha hc hb hac hcb h' with
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
            decide
        · have h' : reciprocalFactor c * reciprocalFactor a * reciprocalFactor b = 3 := by
            nlinarith [h]
          rcases reciprocal_product_sorted c a b hc ha hb hca hab h' with
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
            decide
    · rcases le_total a c with hac | hca
      · have h' : reciprocalFactor b * reciprocalFactor a * reciprocalFactor c = 3 := by
          nlinarith [h]
        rcases reciprocal_product_sorted b a c hb ha hc hba hac h' with
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
          decide
      · rcases le_total b c with hbc | hcb
        · have h' : reciprocalFactor b * reciprocalFactor c * reciprocalFactor a = 3 := by
            nlinarith [h]
          rcases reciprocal_product_sorted b c a hb hc ha hbc hca h' with
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
            decide
        · have h' : reciprocalFactor c * reciprocalFactor b * reciprocalFactor a = 3 := by
            nlinarith [h]
          rcases reciprocal_product_sorted c b a hc hb ha hcb hba h' with
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
            decide
  · intro h
    simp only [reciprocalProductTriples, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl, rfl⟩ <;> norm_num

theorem rational_reciprocal_product_count :
    Nat.card {p : ℤ × ℤ × ℤ // p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      (1 + 1 / (p.1 : ℚ)) * (1 + 1 / (p.2.1 : ℚ)) * (1 + 1 / (p.2.2 : ℚ)) = 3} = 18 := by
  let e : {p : ℤ × ℤ × ℤ // p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      (1 + 1 / (p.1 : ℚ)) * (1 + 1 / (p.2.1 : ℚ)) * (1 + 1 / (p.2.2 : ℚ)) = 3} ≃
      reciprocalProductTriples :=
    Equiv.subtypeEquivRight (fun p => rational_reciprocal_product_classification p.1 p.2.1 p.2.2)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

theorem positive_reciprocal_product_count :
    Nat.card {p : ℤ × ℤ × ℤ // 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      (1 + 1 / (p.1 : ℚ)) * (1 + 1 / (p.2.1 : ℚ)) * (1 + 1 / (p.2.2 : ℚ)) = 3} = 15 := by
  let s := reciprocalProductTriples.filter (fun p => 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2)
  let e : {p : ℤ × ℤ × ℤ // 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 ∧
      (1 + 1 / (p.1 : ℚ)) * (1 + 1 / (p.2.1 : ℚ)) * (1 + 1 / (p.2.2 : ℚ)) = 3} ≃ s :=
    Equiv.subtypeEquivRight (fun p => by
      constructor
      · rintro ⟨ha, hb, hc, h⟩
        exact Finset.mem_filter.mpr
          ⟨(rational_reciprocal_product_classification p.1 p.2.1 p.2.2).mp
            ⟨ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, h⟩, ha, hb, hc⟩
      · intro h
        obtain ⟨hm, ha, hb, hc⟩ := Finset.mem_filter.mp h
        exact ⟨ha, hb, hc,
          ((rational_reciprocal_product_classification p.1 p.2.1 p.2.2).mpr hm).2.2.2⟩)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

private theorem integer_reciprocal_factor_cases (a : ℤ) :
    1 + 1 / a = 0 ∨ 1 + 1 / a = 1 ∨ 1 + 1 / a = 2 := by
  rw [Int.one_ediv]
  split_ifs with ha
  · rcases Int.natAbs_eq_iff.mp ha with rfl | rfl <;> norm_num
  · norm_num

theorem integer_reciprocal_product_impossible (a b c : ℤ) :
    (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) ≠ 3 := by
  rcases integer_reciprocal_factor_cases a with ha | ha | ha <;>
    rcases integer_reciprocal_factor_cases b with hb | hb | hb <;>
    rcases integer_reciprocal_factor_cases c with hc | hc | hc <;>
    rw [ha, hb, hc] <;> norm_num

theorem solution (a b c : ℤ)
    (h : (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) = 3) :
    (a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ b = 3 ∧ c = 2) ∨
      (a = 2 ∧ b = 1 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 1) ∨
      (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1) := by
  exact (integer_reciprocal_product_impossible a b c h).elim
