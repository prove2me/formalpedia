-- Prove2me | solution 1 for lean_workbook_plus_34385
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:43:52.2158+00:00
-- url     : https://prove2.me/submissions/f0a1e0b7-db0a-4237-8ef9-fa528517e2cf

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Filter
open scoped Topology

noncomputable def repeatedQuartic (z : ℂ) : ℂ :=
  z ^ 4 + 5 * z ^ 3 - 3 * z ^ 2 - 17 * z - 10

theorem repeatedQuartic_factorization (z : ℂ) :
    repeatedQuartic z = (z - 2) * (z + 1) ^ 2 * (z + 5) := by
  unfold repeatedQuartic
  ring

theorem repeatedQuartic_roots (z : ℂ) :
    repeatedQuartic z = 0 ↔ z = 2 ∨ z = -1 ∨ z = -5 := by
  rw [repeatedQuartic_factorization]
  simp only [mul_eq_zero, pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0),
    sub_eq_zero, add_eq_zero_iff_eq_neg, or_assoc]

theorem repeatedQuartic_analytic (z : ℂ) : AnalyticAt ℂ repeatedQuartic z := by
  unfold repeatedQuartic
  fun_prop

theorem repeatedQuartic_order_two :
    meromorphicOrderAt repeatedQuartic 2 = (1 : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (repeatedQuartic_analytic 2).meromorphicAt).mpr
  refine ⟨fun z => (z + 1) ^ 2 * (z + 5), by fun_prop, ?_, ?_⟩
  · norm_num
  · filter_upwards with z
    rw [repeatedQuartic_factorization]
    simp only [zpow_one, smul_eq_mul]
    ring

theorem repeatedQuartic_order_neg_one :
    meromorphicOrderAt repeatedQuartic (-1) = (2 : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (repeatedQuartic_analytic (-1)).meromorphicAt).mpr
  refine ⟨fun z => (z - 2) * (z + 5), by fun_prop, ?_, ?_⟩
  · norm_num
  · filter_upwards with z
    change repeatedQuartic z = (z - (-1)) ^ (2 : ℕ) * ((z - 2) * (z + 5))
    rw [repeatedQuartic_factorization]
    ring

theorem repeatedQuartic_order_neg_five :
    meromorphicOrderAt repeatedQuartic (-5) = (1 : WithTop ℤ) := by
  apply (meromorphicOrderAt_eq_int_iff (repeatedQuartic_analytic (-5)).meromorphicAt).mpr
  refine ⟨fun z => (z - 2) * (z + 1) ^ 2, by fun_prop, ?_, ?_⟩
  · norm_num
  · filter_upwards with z
    rw [repeatedQuartic_factorization]
    simp only [zpow_one, smul_eq_mul]
    ring

theorem repeatedQuartic_order_away {z : ℂ} (h₂ : z ≠ 2) (h₁ : z ≠ -1)
    (h₅ : z ≠ -5) : meromorphicOrderAt repeatedQuartic z = 0 := by
  have h := repeatedQuartic_analytic z
  rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr]
  · rfl
  · intro hz
    rcases (repeatedQuartic_roots z).mp hz with hz | hz | hz
    · exact h₂ hz
    · exact h₁ hz
    · exact h₅ hz

theorem repeatedQuartic_orders (z : ℂ) :
    meromorphicOrderAt repeatedQuartic z =
      if z = -1 then 2 else if z = 2 ∨ z = -5 then 1 else 0 := by
  by_cases h₁ : z = -1
  · subst z
    simp only [ite_true, repeatedQuartic_order_neg_one]
  by_cases h₂ : z = 2
  · subst z
    simp only [if_neg h₁, repeatedQuartic_order_two, eq_self, true_or, ite_true]
  by_cases h₅ : z = -5
  · subst z
    simp only [if_neg h₁, repeatedQuartic_order_neg_five, eq_self, or_true, ite_true]
  simp [h₁, h₂, h₅, repeatedQuartic_order_away h₂ h₁ h₅]

theorem repeatedQuartic_roots_real {z : ℂ} (hz : repeatedQuartic z = 0) : z.im = 0 := by
  rcases (repeatedQuartic_roots z).mp hz with rfl | rfl | rfl <;> norm_num

theorem solution (x : ℂ) :
    x ^ 4 + 5 * x ^ 3 - 3 * x ^ 2 - 17 * x - 10 = 0 ↔
      x = 2 ∨ x = -1 ∨ x = -1 ∨ x = -5 := by
  change repeatedQuartic x = 0 ↔ _
  rw [repeatedQuartic_roots]
  tauto

#print axioms repeatedQuartic
#print axioms repeatedQuartic_factorization
#print axioms repeatedQuartic_roots
#print axioms repeatedQuartic_analytic
#print axioms repeatedQuartic_order_two
#print axioms repeatedQuartic_order_neg_one
#print axioms repeatedQuartic_order_neg_five
#print axioms repeatedQuartic_order_away
#print axioms repeatedQuartic_orders
#print axioms repeatedQuartic_roots_real
#print axioms solution
