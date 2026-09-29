-- Prove2me | solution 2 for Catalog.Combinatorics.HybridEvictionAdditiveLaw.net61_calibrated_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:10:50.932367+00:00
-- url     : https://prove2.me/submissions/5e8964a1-b02e-46ba-947a-18921b8a0011

import Mathlib
import Definitions.Def_Combinatorics_HybridEvictionAdditiveLaw
open Finset Catalog.Combinatorics.HybridEvictionAdditiveLaw in
theorem solution {lam : ℝ} (hlam : 0 ≤ lam) {S O : Finset (Fin 4)}
    (hS : IsTopSet (hybrid a4 p4 lam) 2 S) (hO : IsTopSet v4 2 O) :
    retained v4 S = 9384 / 10000 ∧ retained v4 O = 9954 / 10000 ∧
      retained v4 O - retained v4 S = 570 / 10000 := by
  -- the six two-element subsets of `Fin 4`
  have h2 : ∀ T : Finset (Fin 4), T.card = 2 →
      T = {0, 1} ∨ T = {0, 2} ∨ T = {0, 3} ∨ T = {1, 2} ∨ T = {1, 3} ∨ T = {2, 3} := by
    decide
  -- the hybrid score `4+8λ > 3+6λ > 2+4λ > 1+2λ` keeps slots `0, 1`
  have hSeq : S = {0, 1} := by
    have hv : ∀ i j : Fin 4, i ∈ S → j ∉ S → hybrid a4 p4 lam j ≤ hybrid a4 p4 lam i :=
      fun i j hi hj => hS.2 i hi j hj
    rcases h2 S hS.1 with h | h | h | h | h | h <;> subst h
    · rfl
    · have := hv 2 1 (by decide) (by decide)
      simp [hybrid, a4, p4] at this
      linarith
    · have := hv 3 1 (by decide) (by decide)
      simp [hybrid, a4, p4] at this
      linarith
    · have := hv 2 0 (by decide) (by decide)
      simp [hybrid, a4, p4] at this
      linarith
    · have := hv 3 0 (by decide) (by decide)
      simp [hybrid, a4, p4] at this
      linarith
    · have := hv 2 0 (by decide) (by decide)
      simp [hybrid, a4, p4] at this
      linarith
  -- the oracle utilities keep slots `2, 3`
  have hOeq : O = {2, 3} := by
    have hv : ∀ i j : Fin 4, i ∈ O → j ∉ O → v4 j ≤ v4 i :=
      fun i j hi hj => hO.2 i hi j hj
    rcases h2 O hO.1 with h | h | h | h | h | h <;> subst h
    · have := hv 0 2 (by decide) (by decide)
      simp [v4] at this
      norm_num at this
    · have := hv 0 3 (by decide) (by decide)
      simp [v4] at this
      norm_num at this
    · have := hv 0 2 (by decide) (by decide)
      simp [v4] at this
      norm_num at this
    · have := hv 1 3 (by decide) (by decide)
      simp [v4] at this
      norm_num at this
    · have := hv 1 2 (by decide) (by decide)
      simp [v4] at this
      norm_num at this
    · rfl
  subst hSeq
  subst hOeq
  simp [retained, v4]
  norm_num
