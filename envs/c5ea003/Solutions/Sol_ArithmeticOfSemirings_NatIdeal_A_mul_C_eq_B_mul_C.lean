-- Prove2me | solution 1 for ArithmeticOfSemirings.NatIdeal.A_mul_C_eq_B_mul_C
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:53:13.599039+00:00
-- url     : https://prove2.me/submissions/aa44027a-492a-4c1e-a998-9d32e94ec6ef

import Mathlib
import Definitions.Def_Tropical_ArithmeticOfSemiringsIdeals
open ArithmeticOfSemirings NatIdeal in
theorem solution : A * C = B * C := by
  have hA5 : (5 : ℕ) ∈ A := Ideal.subset_span (by norm_num [A])
  have hA17 : (17 : ℕ) ∈ A := Ideal.subset_span (by norm_num [A])
  have hC5 : (5 : ℕ) ∈ C := Ideal.subset_span (by norm_num [C])
  have hC11 : (11 : ℕ) ∈ C := Ideal.subset_span (by norm_num [C])
  have hC19 : (19 : ℕ) ∈ C := Ideal.subset_span (by norm_num [C])
  have hC23 : (23 : ℕ) ∈ C := Ideal.subset_span (by norm_num [C])
  have p25 : (25 : ℕ) ∈ A * C := by
    have h := Ideal.mul_mem_mul hA5 hC5
    norm_num at h
    exact h
  have p95 : (95 : ℕ) ∈ A * C := by
    have h := Ideal.mul_mem_mul hA5 hC19
    norm_num at h
    exact h
  have p115 : (115 : ℕ) ∈ A * C := by
    have h := Ideal.mul_mem_mul hA5 hC23
    norm_num at h
    exact h
  have p187 : (187 : ℕ) ∈ A * C := by
    have h := Ideal.mul_mem_mul hA17 hC11
    norm_num at h
    exact h
  have p323 : (323 : ℕ) ∈ A * C := by
    have h := Ideal.mul_mem_mul hA17 hC19
    norm_num at h
    exact h
  have key43 : ∀ c ∈ C, (43 : ℕ) * c ∈ A * C := by
    intro c hc
    have hc' : c ∈ Ideal.span ({5, 11, 19, 23} : Set ℕ) := hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [show (43 : ℕ) * 5 = 25 + 95 * 2 from by norm_num]
        exact Ideal.add_mem _ p25 (Ideal.mul_mem_right _ _ p95)
      · rw [show (43 : ℕ) * 11 = 323 + 25 * 6 from by norm_num]
        exact Ideal.add_mem _ p323 (Ideal.mul_mem_right _ _ p25)
      · rw [show (43 : ℕ) * 19 = 187 + 115 * 2 + 25 * 16 from by norm_num]
        exact Ideal.add_mem _ (Ideal.add_mem _ p187 (Ideal.mul_mem_right _ _ p115))
          (Ideal.mul_mem_right _ _ p25)
      · rw [show (43 : ℕ) * 23 = 187 * 2 + 115 + 25 * 20 from by norm_num]
        exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ p187) p115)
          (Ideal.mul_mem_right _ _ p25)
    | zero =>
      simpa using Ideal.zero_mem (A * C)
    | add x y hx hy ihx ihy =>
      rw [mul_add]
      exact Ideal.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [smul_eq_mul, show (43 : ℕ) * (a * x) = a * (43 * x) from by ring]
      exact Ideal.mul_mem_left _ a ih
  refine le_antisymm (Ideal.mul_mono ?_ le_rfl) (Ideal.mul_le.mpr ?_)
  · refine Ideal.span_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · intro r hr s hs
    have hr' : r ∈ Ideal.span ({5, 17, 43} : Set ℕ) := hr
    clear hr
    induction hr' using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact Ideal.mul_mem_mul hA5 hs
      · exact Ideal.mul_mem_mul hA17 hs
      · exact key43 s hs
    | zero =>
      simpa using Ideal.zero_mem (A * C)
    | add x y hx hy ihx ihy =>
      rw [add_mul]
      exact Ideal.add_mem _ ihx ihy
    | smul a x hx ih =>
      rw [smul_eq_mul, mul_assoc]
      exact Ideal.mul_mem_left _ a ih
