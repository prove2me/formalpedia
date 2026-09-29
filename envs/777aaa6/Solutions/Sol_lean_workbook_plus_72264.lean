-- Prove2me | solution 1 for lean_workbook_plus_72264
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:22:07.435901+00:00
-- url     : https://prove2.me/submissions/d862b56f-0089-46dd-8e14-f93be8b192ec

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Lattice

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℕ → ℕ) (hf : Set.Finite {n | f n = n}) : ∃ N, ∀ n ≥ N, f n ≠ n := by
  obtain ⟨N, hN⟩ := hf.bddAbove
  refine ⟨N + 1, ?_⟩
  intro n hn heq
  have hbound : n ≤ N := hN heq
  omega
