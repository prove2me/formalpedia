-- Prove2me | solution 1 for lean_workbook_plus_35806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:53:31.654714+00:00
-- url     : https://prove2.me/submissions/a08a1e2a-90f3-4537-afdf-3d9fc3f683de

import Mathlib

set_option autoImplicit false

namespace IdempotentSquareDifference

def Equation {R : Type*} [CommRing R] (f : R → R) : Prop :=
  ∀ m n : R, f (f (m - n)) = f (m ^ 2) + f n - 2 * n * f m

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

theorem at_zero {f : R → R} (h : Equation f) : f 0 = 0 := by
  have hp : f (f (-1)) = f 0 + f 1 - 2 * f 0 := by simpa using h 0 1
  have hn : f (f (-1)) = f 1 + f 0 := by simpa using h (-1) 0
  have heq := hp.symm.trans hn
  have he : (2 : R) * f 0 = 0 := by linear_combination -heq
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

theorem square_invariant {f : R → R} (h : Equation f) (n : R) : f (n ^ 2) = f n := by
  have hp : f (f (-n)) = f n := by simpa [at_zero h] using h 0 n
  have hn : f (f (-n)) = f (n ^ 2) := by simpa [at_zero h] using h (-n) 0
  exact hn.symm.trans hp

theorem idempotent {f : R → R} (h : Equation f) (n : R) : f (f n) = f n := by
  simpa [at_zero h, square_invariant h] using h n 0

theorem reduced_equation {f : R → R} (h : Equation f) (m n : R) :
    f (m - n) = f m + f n - 2 * n * f m := by
  simpa only [idempotent h, square_invariant h] using h m n

theorem diagonal {f : R → R} (h : Equation f) (n : R) : (n - 1) * f n = 0 := by
  have he := reduced_equation h n n
  rw [sub_self, at_zero h] at he
  have hd : (2 : R) * ((n - 1) * f n) = 0 := by linear_combination he
  exact (mul_eq_zero.mp hd).resolve_left (by norm_num)

theorem at_one {f : R → R} (h : Equation f) : f 1 = 0 := by
  have hd := diagonal h (-1)
  have hn : f (-1) = 0 := (mul_eq_zero.mp hd).resolve_left (by norm_num)
  have hs := square_invariant h (-1)
  norm_num at hs
  exact hs.trans hn

theorem every_value_zero {f : R → R} (h : Equation f) (n : R) : f n = 0 := by
  by_cases hn : n = 1
  · simpa only [hn] using at_one h
  · exact (mul_eq_zero.mp (diagonal h n)).resolve_left (sub_ne_zero.mpr hn)

omit [IsDomain R] [CharZero R] in
theorem zero_model : Equation (fun _ : R => (0 : R)) := by
  intro m n
  simp

theorem classification (f : R → R) : Equation f ↔ f = (fun _ => 0) := by
  constructor
  · intro h
    exact funext (every_value_zero h)
  · rintro rfl
    exact zero_model

theorem unique_existence : ∃! f : R → R, Equation f := by
  exact ⟨fun _ => 0, zero_model, fun f hf => (classification f).1 hf⟩

end Domain

theorem integer_classification (f : ℤ → ℤ) :
    (∀ m n : ℤ, f (f (m - n)) = f (m ^ 2) + f n - 2 * n * f m) ↔
      f = (fun _ => 0) := classification f

theorem source_no_solution :
    ¬ ∃ f : ℤ → ℤ, Equation f ∧ 0 < f 1 := by
  rintro ⟨f, hf, hp⟩
  rw [at_one hf] at hp
  exact (lt_irrefl 0) hp

theorem source_solution_set :
    {f : ℤ → ℤ | Equation f ∧ 0 < f 1} = ∅ := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hf
  exact source_no_solution ⟨f, hf⟩

end IdempotentSquareDifference

theorem solution (f : ℤ → ℤ) (hf : f 1 > 0)
    (hf2 : ∀ m n : ℤ, f (f (m - n)) = f (m ^ 2) + f n - 2 * n * f m) :
    ∀ x : ℤ, f x = x + 1 := by
  exact (IdempotentSquareDifference.source_no_solution ⟨f, hf2, hf⟩).elim
