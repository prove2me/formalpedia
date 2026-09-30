-- Prove2me | solution 1 for lean_workbook_plus_35472
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:51:03.278067+00:00
-- url     : https://prove2.me/submissions/1929cca6-d485-4c68-8670-e0533e0987c4

import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ThreeCubesFamily

def family (a t : ℤ) : ℤ × ℤ × ℤ :=
  (a * (1 + 6 * t ^ 3), a * (1 - 6 * t ^ 3), -6 * a * t ^ 2)

theorem identity (a t : ℤ) :
    (family a t).1 ^ 3 + (family a t).2.1 ^ 3 + (family a t).2.2 ^ 3 = 2 * a ^ 3 := by
  simp only [family]
  ring

theorem injective (a : ℤ) (ha : a ≠ 0) : Function.Injective (family a) := by
  intro s t h
  have hfirst := congrArg Prod.fst h
  change a * (1 + 6 * s ^ 3) = a * (1 + 6 * t ^ 3) at hfirst
  have hinner := mul_left_cancel₀ ha hfirst
  have hp : s ^ 3 = t ^ 3 := by omega
  exact (show Odd 3 by decide).pow_injective hp

theorem nondegenerate (a t : ℤ) (ha : a ≠ 0) (ht : t ≠ 0) :
    (family a t).1 ≠ 0 ∧ (family a t).2.1 ≠ 0 ∧ (family a t).2.2 ≠ 0 ∧
    (family a t).1 ≠ (family a t).2.1 ∧
    (family a t).2.1 ≠ (family a t).2.2 ∧
    (family a t).1 ≠ (family a t).2.2 := by
  have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht
  have hthird : -6 * a * t ^ 2 = a * (-6 * t ^ 2) := by ring
  simp only [family]
  refine ⟨mul_ne_zero ha (by omega), mul_ne_zero ha (by omega),
    mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 2 ht), ?_, ?_, ?_⟩
  · intro h
    have hi := mul_left_cancel₀ ha h
    omega
  · rw [hthird]
    intro h
    have hi := mul_left_cancel₀ ha h
    omega
  · rw [hthird]
    intro h
    have hi := mul_left_cancel₀ ha h
    omega

theorem infinitely_many (a : ℤ) (ha : a ≠ 0) :
    Set.Infinite {p : ℤ × ℤ × ℤ |
      p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 = 2 * a ^ 3 ∧
      p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2} := by
  let F : ℕ → ℤ × ℤ × ℤ := fun n => family a (n + 1)
  have hF : Function.Injective F := by
    intro m n h
    have hh := injective a ha h
    exact_mod_cast (show (m : ℤ) = n by omega)
  refine (Set.infinite_range_of_injective hF).mono ?_
  rintro p ⟨n, rfl⟩
  exact ⟨identity a (n + 1), nondegenerate a (n + 1) ha (by omega)⟩

theorem infinitely_many_2000 :
    Set.Infinite {p : ℤ × ℤ × ℤ |
      p.1 ^ 3 + p.2.1 ^ 3 + p.2.2 ^ 3 = 2000 ∧
      p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ p.2.2 ≠ 0 ∧
      p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2} := by
  exact infinitely_many 10 (by norm_num)

end ThreeCubesFamily

theorem solution : ∃ x y z : ℤ, x ^ 3 + y ^ 3 + z ^ 3 = 2000 := by
  refine ⟨70, -50, -60, ?_⟩
  exact ThreeCubesFamily.identity 10 1
