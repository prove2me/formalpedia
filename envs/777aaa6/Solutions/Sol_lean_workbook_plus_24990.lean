-- Prove2me | solution 1 for lean_workbook_plus_24990
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:31:47.50173+00:00
-- url     : https://prove2.me/submissions/6d7f3cea-075b-4a4f-9123-60f8cbfc54d2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

theorem solution (X : Type*) [MetricSpace X] (x : ℕ → X) :
    CauchySeq x ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (x n) (x N) < ε := by
  rw [Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => hN n hn N le_rfl⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    refine ⟨N, ?_⟩
    intro n hn m hm
    have hn' := hN n hn
    have hm' := hN m hm
    calc
      dist (x n) (x m) ≤ dist (x n) (x N) + dist (x N) (x m) := dist_triangle _ _ _
      _ < ε := by rw [dist_comm (x N) (x m)]; linarith

#print axioms solution
