-- Prove2me | solution 1 for TropicalLA.tpow_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:01:35.027251+00:00
-- url     : https://prove2.me/submissions/bf853e4b-4c8b-4435-b2e9-a8729365ceb1

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix

open TropicalLA Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

private lemma sup'_mul_nonneg {α : Type*} [Fintype α] [Nonempty α]
    {c : ℝ} (hc : 0 ≤ c) (f : α → ℝ) :
    univ.sup' univ_nonempty (fun a => c * f a) = c * univ.sup' univ_nonempty f := by
  classical
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le _ _ fun a ha =>
      mul_le_mul_of_nonneg_left (Finset.le_sup' f ha) hc
  · obtain ⟨a0, ha0, hmax⟩ := exists_mem_eq_sup' (univ_nonempty (α := α)) f
    have : c * f a0 ≤ univ.sup' univ_nonempty (fun a => c * f a) :=
      Finset.le_sup' (fun a => c * f a) ha0
    rwa [← hmax] at this

private lemma tmul_scale {c : ℝ} (hc : 0 ≤ c) (A B : Matrix ι ι ℝ) (i j : ι) :
    tmul (fun i j => c * A i j) (fun i j => c * B i j) i j = c * tmul A B i j := by
  simp only [tmul]
  have h : ∀ k, c * A i k + c * B k j = c * (A i k + B k j) := fun _ => by ring
  simp_rw [h]
  exact sup'_mul_nonneg hc _

theorem solution {c : ℝ} (hc : 0 ≤ c) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    tpow (Matrix.of fun i j => c * A i j) m i j = c * tpow A m i j := by
  -- Identify Matrix.of with the lambda matrix
  have hOf : (Matrix.of fun i j => c * A i j : Matrix ι ι ℝ) = fun i j => c * A i j := by
    funext i j; rfl
  -- Prove for the lambda form by induction, then transfer
  have hmat : ∀ m, tpow (fun i j => c * A i j) m = fun i j => c * tpow A m i j := by
    intro m
    induction m with
    | zero => funext i j; simp [tpow]
    | succ m ih =>
        funext i j
        change tmul (tpow (fun i j => c * A i j) m) (fun i j => c * A i j) i j =
          c * tmul (tpow A m) A i j
        rw [ih]
        exact tmul_scale hc (tpow A m) A i j
  simpa [hOf] using congr_fun (congr_fun (hmat m) i) j
