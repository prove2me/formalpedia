-- Prove2me | solution 1 for MeasureTheory.eVariationOn_comp_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:38:10.988087+00:00
-- url     : https://prove2.me/submissions/27d62c54-9615-4850-bcdd-4f4d7aa9a2a0

import Mathlib

universe u v w

theorem solution {α : Type u} [LinearOrder α] {E : Type v} [PseudoEMetricSpace E]
    {F : Type w} [PseudoEMetricSpace F] (f : E → F) (hf : Isometry f)
    (g : α → E) (s : Set α) :
    eVariationOn (f ∘ g) s = eVariationOn g s := by
  unfold eVariationOn
  congr 1
  funext p
  exact Finset.sum_congr rfl fun i _ => hf.edist_eq _ _
