-- Prove2me | solution 1 for Hirsch.polynomial_hirsch_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T04:27:55.833709+00:00
-- url     : https://prove2.me/submissions/22adf93c-51ea-436d-8763-d25f40d8ebdd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_balanced_hpoly_transfer
import Theorems.Thm_Hirsch_balanced_polynomial_bound

open scoped RealInnerProductSpace
open Hirsch

/-- Stationary padding: `DiamLE` is monotone in the walk length. -/
theorem diamLE_mono {E : Type*} [AddCommGroup E] [Module ℝ E]
    (P : Set E) {m L : ℕ} (h : m ≤ L) (hP : DiamLE P m) : DiamLE P L := by
  intro u hu v hv
  obtain ⟨w, hw0, hwm, hs⟩ := hP u hu v hv
  refine ⟨fun i => w (min i m), ?_, ?_, ?_⟩
  · simp [hw0]
  · simp [min_eq_right h, hwm]
  · intro i hi
    by_cases h1 : i + 1 ≤ m
    · have hi' : i < m := Nat.lt_of_succ_le h1
      have hmin_i : min i m = i := min_eq_left (Nat.le_of_lt hi')
      have hmin_i1 : min (i + 1) m = i + 1 := min_eq_left h1
      simpa [hmin_i, hmin_i1] using hs i hi'
    · have hmi : min i m = m := by omega
      have hmi1 : min (i + 1) m = m := by omega
      exact Or.inl (by simp [hmi, hmi1])

/-- Reduction of the polynomial Hirsch conjecture to the balanced subfamily. -/
theorem solution :
    ∃ c k : ℕ, ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (c * (n + d) ^ k) := by
  obtain ⟨C, k, hbal⟩ := balanced_polynomial_bound
  refine ⟨C, k, ?_⟩
  intro d n a b hne hbd
  obtain ⟨D, aQ, bQ, hD, hneQ, hbdQ, htr⟩ := balanced_hpoly_transfer d n a b hne hbd
  have hQ : DiamLE (Hpoly aQ bQ) (C * D ^ k) := hbal D aQ bQ hneQ hbdQ
  have hP : DiamLE (Hpoly a b) (C * D ^ k) := htr (C * D ^ k) hQ
  have hle : C * D ^ k ≤ C * (n + d) ^ k := by
    have : D ≤ n + d := by
      rw [hD]
      omega
    gcongr
  exact diamLE_mono (Hpoly a b) hle hP
