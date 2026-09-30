-- Prove2me | solution 1 for lean_workbook_plus_57454
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:00:40.685976+00:00
-- url     : https://prove2.me/submissions/16d543ca-6ce1-4062-9fa3-7055a6f042e6

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Topology

private theorem tan_pi_div_twelve : Real.tan (Real.pi / 12) = 2 - Real.sqrt 3 := by
  have h4 : Real.cos (Real.pi / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).ne'
  have h6 : Real.cos (Real.pi / 6) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩).ne'
  rw [show Real.pi / 12 = Real.pi / 4 - Real.pi / 6 by ring]
  rw [Real.tan_sub' ⟨Real.cos_ne_zero_iff.mp h4, Real.cos_ne_zero_iff.mp h6⟩,
    Real.tan_pi_div_four, Real.tan_pi_div_six]
  have hs : 0 < Real.sqrt 3 := by positivity
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  field_simp
  nlinarith

private theorem angle_gap_implies_slope_bound {x y : ℝ} (hne : x ≠ y)
    (hgap : |Real.arctan x - Real.arctan y| < Real.pi / 12) :
    |x - y| < (2 - Real.sqrt 3) * |1 + x * y| := by
  have hlow := (abs_lt.mp hgap).1
  have hupp := (abs_lt.mp hgap).2
  have hmem : Real.arctan x - Real.arctan y ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hzero : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hleft : -(Real.pi / 12) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hright : Real.pi / 12 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have htlo := Real.strictMonoOn_tan hleft hmem hlow
  have hthi := Real.strictMonoOn_tan hmem hright hupp
  rw [Real.tan_neg, tan_pi_div_twelve] at htlo
  rw [tan_pi_div_twelve] at hthi
  have htan : Real.tan (Real.arctan x - Real.arctan y) = (x - y) / (1 + x * y) := by
    rw [Real.tan_sub' ⟨Real.arctan_ne_mul_pi_div_two, Real.arctan_ne_mul_pi_div_two⟩,
      Real.tan_arctan, Real.tan_arctan]
  have hd : 1 + x * y ≠ 0 := by
    intro hd
    have htzero : Real.tan (Real.arctan x - Real.arctan y) = Real.tan 0 := by
      rw [htan, hd, div_zero, Real.tan_zero]
    have he := Real.injOn_tan hmem hzero htzero
    exact hne (Real.arctan_injective (sub_eq_zero.mp he))
  have habs : |(x - y) / (1 + x * y)| < 2 - Real.sqrt 3 := by
    rw [← htan]
    exact abs_lt.mpr ⟨htlo, hthi⟩
  rw [abs_div] at habs
  exact (div_lt_iff₀ (abs_pos.mpr hd)).mp habs

theorem thirteen_slopes_distinct (s : Finset ℝ) (hs : s.card = 13) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ |x - y| < (2 - Real.sqrt 3) * |1 + x * y| := by
  classical
  let q : ℝ → ℝ := fun x => 12 * (Real.arctan x + Real.pi / 2) / Real.pi
  have hq0 (x : ℝ) : 0 ≤ q x := by
    dsimp [q]
    apply div_nonneg _ Real.pi_pos.le
    have hx : 0 < Real.arctan x + Real.pi / 2 := by
      linarith [(Real.arctan_mem_Ioo x).1]
    positivity
  have hq12 (x : ℝ) : q x < 12 := by
    dsimp [q]
    apply (div_lt_iff₀ Real.pi_pos).mpr
    linarith [Real.arctan_lt_pi_div_two x]
  let bin : {x // x ∈ s} → Fin 12 := fun x =>
    ⟨⌊q x⌋₊, (Nat.floor_lt (hq0 x)).mpr (by simpa only [Nat.cast_ofNat] using hq12 x)⟩
  have hc : Fintype.card (Fin 12) < Fintype.card {x // x ∈ s} := by
    simp only [Fintype.card_fin, Fintype.card_coe, hs]
    omega
  obtain ⟨x, y, hne, hbin⟩ := Fintype.exists_ne_map_eq_of_card_lt bin hc
  have hfloor : ⌊q x⌋₊ = ⌊q y⌋₊ := congrArg Fin.val hbin
  have hxlo := Nat.floor_le (hq0 x)
  have hxhi := Nat.lt_floor_add_one (q x)
  have hylo := Nat.floor_le (hq0 y)
  have hyhi := Nat.lt_floor_add_one (q y)
  rw [hfloor] at hxlo hxhi
  have hxlo' : (⌊q y⌋₊ : ℝ) * Real.pi ≤ 12 * (Real.arctan x + Real.pi / 2) :=
    (le_div_iff₀ Real.pi_pos).mp hxlo
  have hxhi' : 12 * (Real.arctan x + Real.pi / 2) < ((⌊q y⌋₊ : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hxhi
  have hylo' : (⌊q y⌋₊ : ℝ) * Real.pi ≤ 12 * (Real.arctan y + Real.pi / 2) :=
    (le_div_iff₀ Real.pi_pos).mp hylo
  have hyhi' : 12 * (Real.arctan y + Real.pi / 2) < ((⌊q y⌋₊ : ℝ) + 1) * Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp hyhi
  have hgap : |Real.arctan x - Real.arctan y| < Real.pi / 12 := by
    apply abs_lt.mpr
    constructor <;> nlinarith
  have hxy : (x : ℝ) ≠ y := fun he => hne (Subtype.ext he)
  exact ⟨x, x.property, y, y.property, hxy, angle_gap_implies_slope_bound hxy hgap⟩

theorem solution (s : Finset ℝ) (hs : s.card = 13) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ (abs (x - y) ≤ (2 - Real.sqrt 3) * abs (1 + x * y)) := by
  obtain ⟨x, hx, y, hy, _, hxy⟩ := thirteen_slopes_distinct s hs
  exact ⟨x, y, hx, hy, hxy.le⟩

#print axioms thirteen_slopes_distinct
#print axioms solution
