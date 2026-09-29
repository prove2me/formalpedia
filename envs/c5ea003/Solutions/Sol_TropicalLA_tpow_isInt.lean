-- Prove2me | solution 1 for TropicalLA.tpow_isInt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T21:48:42.476481+00:00
-- url     : https://prove2.me/submissions/75a6a6b3-75bb-4c63-ba12-192cf21cbe86

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalCyclicity
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
open TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : ∀ i j, ∃ z : ℤ, A i j = (z : ℝ)) (m : ℕ) (i j : ι) : ∃ z : ℤ, tpow A m i j = (z : ℝ) := by
  induction m generalizing i j with
  | zero => exact hA i j
  | succ m ih =>
    -- a tropical product entry is a maximum, attained at some index `k`, of integer sums
    show ∃ z : ℤ, tmul (tpow A m) A i j = (z : ℝ)
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k => tpow A m i k + A k j)
    obtain ⟨z₁, hz₁⟩ := ih i k
    obtain ⟨z₂, hz₂⟩ := hA k j
    refine ⟨z₁ + z₂, ?_⟩
    simp only [tmul]
    rw [hk, hz₁, hz₂]
    push_cast
    ring
