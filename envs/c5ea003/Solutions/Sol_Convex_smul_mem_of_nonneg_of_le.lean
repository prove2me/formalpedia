-- Prove2me | solution 1 for Convex.smul_mem_of_nonneg_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T13:37:10.984645+00:00
-- url     : https://prove2.me/submissions/4ee116d7-78df-4f0a-8c0f-67bb7802d452

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {v : E} {x a : ℝ}
    (hzero : (0 : E) ∈ s) (ha : a • v ∈ s) (hx : 0 ≤ x) (hxa : x ≤ a) :
    x • v ∈ s := by
  by_cases ha0 : a = 0
  · have hx0 : x = 0 := by linarith
    simpa [hx0] using hzero
  · have hapos : 0 < a := lt_of_le_of_ne (hx.trans hxa) (Ne.symm ha0)
    have hratio : x / a ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx hapos.le, (div_le_one hapos).2 hxa⟩
    have hmem := hs.smul_mem_of_zero_mem hzero ha hratio
    simpa only [smul_smul, div_mul_cancel₀ x ha0] using hmem
