-- Prove2me | solution 1 for lean_workbook_plus_18282
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:31:52.98601+00:00
-- url     : https://prove2.me/submissions/c85ee14d-db45-4b95-bdfb-83e3f77e27ac

import Mathlib

namespace ReflectedMonotoneCubics

def oddCubic (p x : ℝ) : ℝ := x ^ 3 + p * x

theorem odd_cubic_gap (p x y : ℝ) :
    oddCubic p y - oddCubic p x = (y - x) * (x ^ 2 + x * y + y ^ 2 + p) := by
  unfold oddCubic
  ring

theorem odd_cubic_strictMono (p : ℝ) (hp : 0 < p) : StrictMono (oddCubic p) := by
  intro x y hxy
  have hq : 0 < x ^ 2 + x * y + y ^ 2 + p := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x + y)]
  have hprod := mul_pos (sub_pos.mpr hxy) hq
  rw [← odd_cubic_gap] at hprod
  exact sub_pos.mp hprod

theorem odd_cubic_neg (p x : ℝ) : oddCubic p (-x) = -oddCubic p x := by
  unfold oddCubic
  ring

theorem opposite_values (p t x y : ℝ) (hp : 0 < p)
    (hx : oddCubic p x = t) (hy : oddCubic p y = -t) : x + y = 0 := by
  have hn : oddCubic p (-y) = t := by rw [odd_cubic_neg, hy]; ring
  have he := (odd_cubic_strictMono p hp).injective (hx.trans hn.symm)
  linarith

def first (x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 + 5 * x - 17

def second (x : ℝ) : ℝ := x ^ 3 - 3 * x ^ 2 + 5 * x + 11

theorem shifted_identities (x : ℝ) :
    first x = oddCubic 2 (x - 1) - 14 ∧
      second x = oddCubic 2 (x - 1) + 14 ∧ second (2 - x) = -first x := by
  unfold first second oddCubic
  constructor
  · ring
  · constructor <;> ring

theorem root_sum (a b : ℝ) (ha : first a = 0) (hb : second b = 0) : a + b = 2 := by
  have h1 : oddCubic 2 (a - 1) = 14 := by linarith [(shifted_identities a).1]
  have h2 : oddCubic 2 (b - 1) = -14 := by linarith [(shifted_identities b).2.1]
  have h := opposite_values 2 14 (a - 1) (b - 1) (by norm_num) h1 h2
  linarith

theorem first_strictMono : StrictMono first := by
  intro x y hxy
  have h := odd_cubic_strictMono 2 (by norm_num) (sub_lt_sub_right hxy 1)
  linarith [(shifted_identities x).1, (shifted_identities y).1]

theorem first_root_exists : ∃ a : ℝ, 3 < a ∧ a < 4 ∧ first a = 0 := by
  have hc : Continuous first := by unfold first; fun_prop
  have h3 : first 3 = -2 := by unfold first; ring
  have h4 : first 4 = 19 := by unfold first; ring
  obtain ⟨a, hai, ha⟩ := intermediate_value_Icc (by norm_num : (3 : ℝ) ≤ 4)
    hc.continuousOn (by rw [h3, h4]; norm_num : (0 : ℝ) ∈ Set.Icc (first 3) (first 4))
  have hn3 : a ≠ 3 := by rintro rfl; rw [h3] at ha; norm_num at ha
  have hn4 : a ≠ 4 := by rintro rfl; rw [h4] at ha; norm_num at ha
  exact ⟨a, lt_of_le_of_ne hai.1 hn3.symm, lt_of_le_of_ne hai.2 hn4, ha⟩

theorem full_source_classification :
    ∃ a : ℝ, 3 < a ∧ a < 4 ∧ -2 < 2 - a ∧ 2 - a < -1 ∧
      ∀ x y : ℝ, (first x = 0 ∧ second y = 0) ↔ x = a ∧ y = 2 - a := by
  obtain ⟨a, ha3, ha4, ha⟩ := first_root_exists
  have hb : second (2 - a) = 0 := by rw [(shifted_identities a).2.2, ha]; ring
  refine ⟨a, ha3, ha4, by linarith, by linarith, ?_⟩
  intro x y
  constructor
  · rintro ⟨hx, hy⟩
    have he := first_strictMono.injective (hx.trans ha.symm)
    have hs := root_sum x y hx hy
    exact ⟨he, by linarith⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨ha, hb⟩

theorem unique_root_pair : ∃! p : ℝ × ℝ, first p.1 = 0 ∧ second p.2 = 0 := by
  obtain ⟨a, _, _, _, _, hclass⟩ := full_source_classification
  refine ⟨(a, 2 - a), (hclass a (2 - a)).mpr ⟨rfl, rfl⟩, ?_⟩
  rintro ⟨x, y⟩ hp
  obtain ⟨rfl, rfl⟩ := (hclass x y).mp hp
  rfl

end ReflectedMonotoneCubics

theorem solution (α β : ℝ)
    (h₁ : α ^ 3 - 3 * α ^ 2 + 5 * α - 17 = 0)
    (h₂ : β ^ 3 - 3 * β ^ 2 + 5 * β + 11 = 0) : α + β = 2 := by
  exact ReflectedMonotoneCubics.root_sum α β h₁ h₂

#print axioms ReflectedMonotoneCubics.odd_cubic_gap
#print axioms ReflectedMonotoneCubics.odd_cubic_strictMono
#print axioms ReflectedMonotoneCubics.odd_cubic_neg
#print axioms ReflectedMonotoneCubics.opposite_values
#print axioms ReflectedMonotoneCubics.shifted_identities
#print axioms ReflectedMonotoneCubics.root_sum
#print axioms ReflectedMonotoneCubics.first_strictMono
#print axioms ReflectedMonotoneCubics.first_root_exists
#print axioms ReflectedMonotoneCubics.full_source_classification
#print axioms ReflectedMonotoneCubics.unique_root_pair
#print axioms solution
