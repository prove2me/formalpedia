-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.Ladder.ladder_properThreeEdgeColoring
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:55:41.189113+00:00
-- url     : https://prove2.me/submissions/5478485e-fa38-477f-a6d3-2817deb442a3

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsLadder
open Bridges.InfiniteCubicMatchings Bridges.InfiniteCubicMatchings.Ladder in
theorem solution : ProperThreeEdgeColoring ladder := by
  refine ⟨![rung, evenRail, oddRail], ?_, ?_⟩
  · -- distinct colour classes share no edge: compare the columns of the endpoints
    intro i j hij
    rw [Set.disjoint_left]
    rintro e ⟨⟨n, b⟩, rfl⟩ ⟨⟨m, c⟩, hw⟩
    have h1 := congrArg (Sym2.map Prod.fst) hw
    simp only [Sym2.map_mk] at h1
    rw [Sym2.eq_iff] at h1
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
        rung, evenRail, oddRail] at h1 <;>
      (try split_ifs at h1) <;> simp only at h1 <;> omega
  · -- every rung and every rail lies in one of the three classes
    intro e he
    induction e using Sym2.ind with
    | h p q =>
    obtain ⟨n, b⟩ := p
    obtain ⟨m, c⟩ := q
    rw [SimpleGraph.mem_edgeSet] at he
    change (n = m ∧ b ≠ c) ∨ (b = c ∧ (m = n + 1 ∨ n = m + 1)) at he
    rcases he with ⟨rfl, hbc⟩ | ⟨rfl, hnm | hnm⟩
    · have hc : c = !b := by cases b <;> cases c <;> simp_all
      subst hc
      exact ⟨0, (n, b), rfl⟩
    · subst hnm
      by_cases h : n % 2 = 0
      · exact ⟨1, (n, b), by simp [evenRail, h]⟩
      · have h' : ¬ (2 : ℤ) ∣ n := by omega
        exact ⟨2, (n, b), by simp [oddRail, h, h']⟩
    · subst hnm
      by_cases h : m % 2 = 0
      · exact ⟨1, (m, b), by rw [Sym2.eq_swap]; simp [evenRail, h]⟩
      · have h' : ¬ (2 : ℤ) ∣ m := by omega
        exact ⟨2, (m, b), by rw [Sym2.eq_swap]; simp [oddRail, h, h']⟩
