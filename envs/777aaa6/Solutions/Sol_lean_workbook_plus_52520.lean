-- Prove2me | solution 1 for lean_workbook_plus_52520
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:40:35.078513+00:00
-- url     : https://prove2.me/submissions/620efee0-bae2-49fe-903f-e05169aa010c

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

def triangleCyclicNumerator (a b c : ℝ) : ℝ :=
  a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * a ^ 2 -
    a * b * c * (a ^ 2 + b ^ 2 + c ^ 2)

theorem triangle_cyclic_substitution (x y z : ℝ) :
    triangleCyclicNumerator (x + y) (y + z) (z + x) =
      x * (x ^ 2 - y ^ 2) ^ 2 + y * (y ^ 2 - z ^ 2) ^ 2 +
        z * (z ^ 2 - x ^ 2) ^ 2 := by
  unfold triangleCyclicNumerator
  ring

theorem triangle_cyclic_parameter_nonnegative (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ triangleCyclicNumerator (x + y) (y + z) (z + x) := by
  rw [triangle_cyclic_substitution]
  positivity

theorem triangle_cyclic_parameter_zero (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    triangleCyclicNumerator (x + y) (y + z) (z + x) = 0 ↔
      x = y ∧ y = z := by
  rw [triangle_cyclic_substitution]
  constructor
  · intro h
    have hn1 : 0 ≤ x * (x ^ 2 - y ^ 2) ^ 2 := by positivity
    have hn2 : 0 ≤ y * (y ^ 2 - z ^ 2) ^ 2 := by positivity
    have hn3 : 0 ≤ z * (z ^ 2 - x ^ 2) ^ 2 := by positivity
    have h1 : x * (x ^ 2 - y ^ 2) ^ 2 = 0 := by linarith
    have h2 : y * (y ^ 2 - z ^ 2) ^ 2 = 0 := by linarith
    have hs1 : (x ^ 2 - y ^ 2) ^ 2 = 0 :=
      (mul_eq_zero.mp h1).resolve_left (ne_of_gt hx)
    have hs2 : (y ^ 2 - z ^ 2) ^ 2 = 0 :=
      (mul_eq_zero.mp h2).resolve_left (ne_of_gt hy)
    have hxy : x ^ 2 - y ^ 2 = 0 := by simpa using hs1
    have hyz : y ^ 2 - z ^ 2 = 0 := by simpa using hs2
    exact ⟨(sq_eq_sq₀ hx.le hy.le).mp (by linarith),
      (sq_eq_sq₀ hy.le hz.le).mp (by linarith)⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem triangle_cyclic_rational_gap (a b c : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    a ^ 2 * (b / c - 1) + b ^ 2 * (c / a - 1) + c ^ 2 * (a / b - 1) =
      triangleCyclicNumerator a b c / (a * b * c) := by
  unfold triangleCyclicNumerator
  field_simp
  <;> ring

theorem triangle_cyclic_nonnegative (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : c ≤ a + b) (h2 : b ≤ a + c) (h3 : a ≤ b + c) :
    0 ≤ a ^ 2 * (b / c - 1) + b ^ 2 * (c / a - 1) +
      c ^ 2 * (a / b - 1) := by
  let x := (a + c - b) / 2
  let y := (a + b - c) / 2
  let z := (b + c - a) / 2
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hxy : x + y = a := by dsimp [x, y]; ring
  have hyz : y + z = b := by dsimp [y, z]; ring
  have hzx : z + x = c := by dsimp [z, x]; ring
  have hn := triangle_cyclic_parameter_nonnegative x y z hx hy hz
  rw [hxy, hyz, hzx] at hn
  rw [triangle_cyclic_rational_gap a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)]
  exact div_nonneg hn (by positivity)

theorem triangle_cyclic_equality (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : c < a + b) (h2 : b < a + c) (h3 : a < b + c) :
    a ^ 2 * (b / c - 1) + b ^ 2 * (c / a - 1) +
      c ^ 2 * (a / b - 1) = 0 ↔ a = b ∧ b = c := by
  constructor
  · intro h
    rw [triangle_cyclic_rational_gap a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)] at h
    have hp : triangleCyclicNumerator a b c = 0 :=
      (div_eq_zero_iff.mp h).resolve_right (by positivity)
    let x := (a + c - b) / 2
    let y := (a + b - c) / 2
    let z := (b + c - a) / 2
    have hx : 0 < x := by dsimp [x]; linarith
    have hy : 0 < y := by dsimp [y]; linarith
    have hz : 0 < z := by dsimp [z]; linarith
    have hxy : x + y = a := by dsimp [x, y]; ring
    have hyz : y + z = b := by dsimp [y, z]; ring
    have hzx : z + x = c := by dsimp [z, x]; ring
    have he : x = y ∧ y = z := (triangle_cyclic_parameter_zero x y z hx hy hz).mp
      (by rwa [hxy, hyz, hzx])
    constructor <;> linarith [he.1, he.2]
  · rintro ⟨rfl, rfl⟩
    simp [ne_of_gt hc]

theorem solution (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : c < a + b) (h₂ : b < a + c) (h₃ : a < b + c) :
    0 ≤ a ^ 2 * (b / c - 1) + b ^ 2 * (c / a - 1) +
      c ^ 2 * (a / b - 1) :=
  triangle_cyclic_nonnegative a b c h₀.1 h₀.2.1 h₀.2.2 h₁.le h₂.le h₃.le

#print axioms solution
#print axioms triangle_cyclic_nonnegative
#print axioms triangle_cyclic_equality
