-- Prove2me | solution 1 for lean_workbook_plus_55442
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:18:28.828348+00:00
-- url     : https://prove2.me/submissions/0db26f45-0c90-4643-a5ba-fd763c3c9c10

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem range_add_closed (f : ℤ → ℝ)
    (hsub : ∀ m n : ℤ, ∃ k : ℤ, f m - f n = f k) :
    ∀ m n : ℤ, ∃ k : ℤ, f m + f n = f k := by
  obtain ⟨z, hz⟩ := hsub 0 0
  have hz0 : f z = 0 := by linarith
  intro m n
  obtain ⟨j, hj⟩ := hsub z n
  obtain ⟨k, hk⟩ := hsub m j
  exact ⟨k, by linarith⟩

theorem constant_step (f : ℤ → ℝ) (hf : StrictMono f)
    (hsub : ∀ m n : ℤ, ∃ k : ℤ, f m - f n = f k)
    (z : ℤ) (hz : f z = 0) :
    0 < f (z + 1) ∧ ∀ n : ℤ, f (n + 1) = f n + f (z + 1) := by
  have hc : 0 < f (z + 1) := by
    have h := hf (show z < z + 1 by omega)
    linarith
  refine ⟨hc, ?_⟩
  intro n
  obtain ⟨j, hj⟩ := hsub (n + 1) n
  have hjpos : f z < f j := by
    have h := hf (show n < n + 1 by omega)
    linarith
  have hzj : z < j := hf.lt_iff_lt.mp hjpos
  have hlo := hf.monotone (show z + 1 ≤ j by omega)
  obtain ⟨k, hk⟩ := range_add_closed f hsub n (z + 1)
  have hnk : n < k := hf.lt_iff_lt.mp (by linarith)
  have hhi := hf.monotone (show n + 1 ≤ k by omega)
  linarith

theorem integer_step_formula (f : ℤ → ℝ) (c : ℝ)
    (hstep : ∀ n : ℤ, f (n + 1) = f n + c) :
    ∀ n : ℤ, f n = f 0 + (n : ℝ) * c := by
  intro n
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [hstep]
    push_cast at ih ⊢
    linarith
  | pred n ih =>
    have h := hstep (-(n : ℤ) - 1)
    have he : -(n : ℤ) - 1 + 1 = -n := by ring
    rw [he] at h
    push_cast at ih ⊢
    linarith

theorem affine_lattice_classification (f : ℤ → ℝ) :
    ((∀ m n : ℤ, m < n → f m < f n) ∧
      (∀ m n : ℤ, ∃ k : ℤ, f m - f n = f k)) ↔
    ∃ c : ℝ, 0 < c ∧ ∃ k : ℤ, ∀ n : ℤ, f n = c * ((n + k : ℤ) : ℝ) := by
  constructor
  · rintro ⟨hf, hsub⟩
    have hmono : StrictMono f := fun _ _ h => hf _ _ h
    obtain ⟨z, hz⟩ := hsub 0 0
    have hz0 : f z = 0 := by linarith
    obtain ⟨hc, hstep⟩ := constant_step f hmono hsub z hz0
    have hlinear := integer_step_formula f (f (z + 1)) hstep
    refine ⟨f (z + 1), hc, -z, ?_⟩
    intro n
    have hn := hlinear n
    have hzero := hlinear z
    push_cast
    nlinarith
  · rintro ⟨c, hc, k, h⟩
    constructor
    · intro m n hmn
      rw [h m, h n]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast (show m + k < n + k by omega)) hc
    · intro m n
      refine ⟨m - n - k, ?_⟩
      rw [h m, h n, h (m - n - k)]
      push_cast
      ring

theorem solution : ∃ f : ℤ → ℝ,
    (∀ m n : ℤ, m < n → f m < f n) ∧
    (∀ m n : ℤ, ∃ k : ℤ, f m - f n = f k) := by
  refine ⟨fun n => (n : ℝ), (affine_lattice_classification _).mpr ?_⟩
  refine ⟨1, by norm_num, 0, ?_⟩
  intro n
  simp
