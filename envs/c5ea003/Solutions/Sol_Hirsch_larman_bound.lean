-- Prove2me | solution 1 for Hirsch.larman_bound
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T05:07:03.516741+00:00
-- url     : https://prove2.me/submissions/a83b2391-d374-45dc-8d33-e35b48abfd3f

import Mathlib
import Definitions.Def_Hirsch_model
import Theorems.Thm_Hirsch_dimension_three_bound
import Theorems.Thm_Hirsch_larman_high_dimension

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

/-- Larman's bound in dimensions at most three is the Hirsch bound `n - d`,
which is at most `n = n * 2^(d-3)`. Higher dimensions remain the inductive
content of Larman's theorem. -/
theorem solution (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3)) := by
  if hd : d ≤ 3 then
    have h3 := dimension_three_bound d n hd a b hne hbd
    have hle : n - d ≤ n * 2 ^ (d - 3) := by
      have hpow : d - 3 = 0 := Nat.sub_eq_zero_of_le hd
      simp [hpow]
    exact diamLE_mono (Hpoly a b) hle h3
  else
    have hd4 : 4 ≤ d := by omega
    exact larman_high_dimension d n hd4 a b hne hbd
