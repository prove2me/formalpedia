-- Prove2me | solution 1 for lean_workbook_plus_27728
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:34.305617+00:00
-- url     : https://prove2.me/submissions/5bbb67fe-88e0-4d91-964c-e2377d2360a2

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

open Filter Topology

theorem solution (a : ℝ) (f g h : ℝ → ℝ) (hf : ∀ x, f x ≤ g x)
    (hg : ∀ x, g x ≤ h x) (h1 : ContinuousAt f a) (h2 : ContinuousAt h a)
    (h3 : f a = h a) : ContinuousAt g a := by
  have ha : g a = f a := le_antisymm (by linarith [hg a]) (hf a)
  have h2' : Tendsto h (𝓝 a) (𝓝 (f a)) := by simpa only [h3] using h2
  have hs : Tendsto g (𝓝 a) (𝓝 (f a)) := h1.squeeze h2' hf hg
  simpa only [ContinuousAt, ha] using hs

#print axioms solution
