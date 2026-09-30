-- Prove2me | solution 1 for lean_workbook_plus_82031
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:52:24.627824+00:00
-- url     : https://prove2.me/submissions/6fdeac02-7544-4138-a9b2-5cf4dc68a3cf

import Mathlib

namespace CyclicQuarticSharpMaximum

def cyclic (a b c : ℝ) : ℝ := a ^ 3 * b + b ^ 3 * c + c ^ 3 * a

def gap (a b c : ℝ) : ℝ := 27 * (a + b + c) ^ 4 - 256 * cyclic a b c

def boundary (x y : ℝ) : ℝ :=
  (x - 3 * y) ^ 2 * (27 * x ^ 2 + 14 * x * y + 3 * y ^ 2)

theorem boundary_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ boundary x y := by
  unfold boundary
  positivity

theorem translation_identity (x y t : ℝ) :
    gap (t + x) (t + y) t = boundary x y + 1419 * t ^ 4 +
      1892 * t ^ 3 * (x + y) +
      t ^ 2 * (690 * x ^ 2 + 2148 * x * y + 690 * y ^ 2) +
      t * (68 * x ^ 3 + 204 * x ^ 2 * y + 972 * x * y ^ 2 + 68 * y ^ 3) := by
  unfold gap cyclic boundary
  ring

theorem minimum_remainder {a b c : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (hcb : c ≤ b) :
    boundary (a - c) (b - c) + 1419 * c ^ 4 ≤ gap a b c := by
  have hx : 0 ≤ a - c := sub_nonneg.mpr hca
  have hy : 0 ≤ b - c := sub_nonneg.mpr hcb
  have hi := translation_identity (a - c) (b - c) c
  have hax : c + (a - c) = a := by ring
  have hby : c + (b - c) = b := by ring
  rw [hax, hby] at hi
  have htail : 0 ≤ 1892 * c ^ 3 * ((a - c) + (b - c)) +
      c ^ 2 * (690 * (a - c) ^ 2 + 2148 * (a - c) * (b - c) +
        690 * (b - c) ^ 2) +
      c * (68 * (a - c) ^ 3 + 204 * (a - c) ^ 2 * (b - c) +
        972 * (a - c) * (b - c) ^ 2 + 68 * (b - c) ^ 3) := by positivity
  linarith

theorem gap_rotate (a b c : ℝ) : gap b c a = gap a b c := by
  unfold gap cyclic
  ring

theorem homogeneous_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    256 * cyclic a b c ≤ 27 * (a + b + c) ^ 4 := by
  have hmin {x y t : ℝ} (ht : 0 ≤ t) (htx : t ≤ x) (hty : t ≤ y) :
      0 ≤ gap x y t := by
    have h := minimum_remainder ht htx hty
    have hboundary := boundary_nonneg (sub_nonneg.mpr htx) (sub_nonneg.mpr hty)
    have hpow := pow_nonneg ht 4
    linarith
  have hgap : 0 ≤ gap a b c := by
    rcases le_total c a with hca | hac
    · rcases le_total c b with hcb | hbc
      · exact hmin hc hca hcb
      · have h := hmin hb hbc (hbc.trans hca)
        simpa only [gap_rotate] using h
    · rcases le_total a b with hab | hba
      · have h := hmin ha hab hac
        simpa only [gap_rotate] using h
      · have h := hmin hb (hba.trans hac) hba
        simpa only [gap_rotate] using h
  exact sub_nonneg.mp hgap

theorem normalized_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 3) : cyclic a b c ≤ 2187 / 256 := by
  have h := homogeneous_bound a b c ha hb hc
  rw [hs] at h
  norm_num at h
  linarith

theorem minimum_equality {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) (hs : a + b + c = 3) (he : gap a b c = 0) :
    a = 9 / 4 ∧ b = 3 / 4 ∧ c = 0 := by
  have hr := minimum_remainder hc hca hcb
  have hboundary := boundary_nonneg (sub_nonneg.mpr hca) (sub_nonneg.mpr hcb)
  have hc4 : c ^ 4 = 0 := by nlinarith [pow_nonneg hc 4]
  have hc0 : c = 0 := (pow_eq_zero_iff (by decide : (4 : ℕ) ≠ 0)).mp hc4
  subst c
  simp only [sub_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, add_zero] at hr
  have hab : a + b = 3 := by linarith
  have habsq : (a + b) ^ 2 = 9 := by rw [hab]; norm_num
  have hcoeff : 0 < 27 * a ^ 2 + 14 * a * b + 3 * b ^ 2 := by
    nlinarith [sq_nonneg a, mul_nonneg ha hb]
  have hz : boundary a b = 0 := le_antisymm (by linarith) (boundary_nonneg ha hb)
  unfold boundary at hz
  have hsq := (mul_eq_zero.mp hz).resolve_right (ne_of_gt hcoeff)
  have hratio := sq_eq_zero_iff.mp hsq
  refine ⟨?_, ?_, rfl⟩ <;> linarith

theorem maximizers (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = 3) :
    cyclic a b c = 2187 / 256 ↔
      (a = 9 / 4 ∧ b = 3 / 4 ∧ c = 0) ∨
      (a = 0 ∧ b = 9 / 4 ∧ c = 3 / 4) ∨
      (a = 3 / 4 ∧ b = 0 ∧ c = 9 / 4) := by
  constructor
  · intro h
    have he : gap a b c = 0 := by unfold gap; rw [hs, h]; ring
    rcases le_total c a with hca | hac
    · rcases le_total c b with hcb | hbc
      · exact Or.inl (minimum_equality ha hb hc hca hcb hs he)
      · have he' : gap c a b = 0 := by simpa only [gap_rotate] using he
        obtain ⟨hc', ha', hb'⟩ := minimum_equality hc ha hb hbc (hbc.trans hca)
          (by linarith : c + a + b = 3) he'
        exact Or.inr (Or.inr ⟨ha', hb', hc'⟩)
    · rcases le_total a b with hab | hba
      · have he' : gap b c a = 0 := by simpa only [gap_rotate] using he
        obtain ⟨hb', hc', ha'⟩ := minimum_equality hb hc ha hab hac
          (by linarith : b + c + a = 3) he'
        exact Or.inr (Or.inl ⟨ha', hb', hc'⟩)
      · have he' : gap c a b = 0 := by simpa only [gap_rotate] using he
        obtain ⟨hc', ha', hb'⟩ := minimum_equality hc ha hb (hba.trans hac) hba
          (by linarith : c + a + b = 3) he'
        exact Or.inr (Or.inr ⟨ha', hb', hc'⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;>
      unfold cyclic <;> ring

theorem attained_maximum : ∃ a b c : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a + b + c = 3 ∧ cyclic a b c = 2187 / 256 := by
  refine ⟨9 / 4, 3 / 4, 0, ?_, ?_, le_rfl, ?_, ?_⟩
  · norm_num
  · norm_num
  · ring
  · unfold cyclic; ring

end CyclicQuarticSharpMaximum

theorem solution (a b c V : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 3) (hV : V = a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) :
    (a = 4 / 3 ∧ b = 4 / 3 ∧ c = 4 / 3 → V = 27 * (4 / 27) ^ 4) ∧
    (a = 4 / 3 ∧ b = 4 / 3 ∧ c = 4 / 3 → ∀ x y z : ℝ,
      x + y + z = 3 ∧ x ^ 3 * y + y ^ 3 * z + z ^ 3 * x ≤ V) := by
  have hn : ¬ (a = 4 / 3 ∧ b = 4 / 3 ∧ c = 4 / 3) := by
    rintro ⟨rfl, rfl, rfl⟩
    norm_num at habc
  exact ⟨fun h => (hn h).elim, fun h => (hn h).elim⟩

#print axioms CyclicQuarticSharpMaximum.translation_identity
#print axioms CyclicQuarticSharpMaximum.minimum_remainder
#print axioms CyclicQuarticSharpMaximum.homogeneous_bound
#print axioms CyclicQuarticSharpMaximum.normalized_bound
#print axioms CyclicQuarticSharpMaximum.minimum_equality
#print axioms CyclicQuarticSharpMaximum.maximizers
#print axioms CyclicQuarticSharpMaximum.attained_maximum
#print axioms solution
