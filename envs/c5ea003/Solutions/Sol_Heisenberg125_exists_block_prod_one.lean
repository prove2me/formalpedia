-- Prove2me | solution 1 for Heisenberg125.exists_block_prod_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:42:24.75717+00:00
-- url     : https://prove2.me/submissions/36c6f890-98c8-4b6f-8d62-3f8bc6273390

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 in
theorem solution {G : Type*} [Group G] {L : List G} {i j : ℕ} (hij : i < j) (hj : j ≤ L.length)
    (h : (L.take i).prod = (L.take j).prod) :
    ∃ T : List G, T.Sublist L ∧ T ≠ [] ∧ T.prod = 1 := by
  refine ⟨(L.take j).drop i, ?_, ?_, ?_⟩
  · exact ((L.take j).drop_sublist i).trans (L.take_sublist j)
  · have hlen : ((L.take j).drop i).length = j - i := by
      simp [min_eq_left hj]
    intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  · have happ : (L.take i) ++ ((L.take j).drop i) = L.take j := by
      have htt : (L.take j).take i = L.take i := by
        rw [List.take_take, min_eq_left hij.le]
      rw [← htt, List.take_append_drop]
    have hsplit : (L.take i).prod * ((L.take j).drop i).prod = (L.take j).prod := by
      rw [← List.prod_append, happ]
    rw [h] at hsplit
    have hcancel : (L.take j).prod * ((L.take j).drop i).prod = (L.take j).prod * 1 := by
      rw [mul_one]
      exact hsplit
    exact mul_left_cancel hcancel
