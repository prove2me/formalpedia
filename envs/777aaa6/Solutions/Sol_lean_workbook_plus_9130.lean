-- Prove2me | solution 1 for lean_workbook_plus_9130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:32:18.044061+00:00
-- url     : https://prove2.me/submissions/954f439f-5cd2-47c4-b168-2726be3af4e8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic

theorem solution {f : ℝ → ℝ} {x : ℝ} :
    UniformContinuousOn f (Set.Icc x (x + 1)) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ t1 t2 : ℝ, t1 ∈ Set.Icc x (x + 1) ∧
        t2 ∈ Set.Icc x (x + 1) ∧ |t1 - t2| < δ → |f t1 - f t2| < ε := by
  rw [Metric.uniformContinuousOn_iff]
  simp only [Real.dist_eq]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδf⟩ := h ε hε
    exact ⟨δ, hδ, fun t1 t2 ht => hδf t1 ht.1 t2 ht.2.1 ht.2.2⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδf⟩ := h ε hε
    exact ⟨δ, hδ, fun t1 ht1 t2 ht2 ht => hδf t1 t2 ⟨ht1, ht2, ht⟩⟩

#print axioms solution
