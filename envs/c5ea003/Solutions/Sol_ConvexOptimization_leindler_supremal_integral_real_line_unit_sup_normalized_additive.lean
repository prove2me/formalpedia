-- Prove2me | solution 1 for ConvexOptimization.leindler_supremal_integral_real_line_unit_sup_normalized_additive
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T07:09:24.153763+00:00
-- url     : https://prove2.me/submissions/1c6941ca-c33d-4309-a975-f21ccde6abcd

import Theorems.Thm_ConvexOptimization_leindler_additive_lower_integral_real_line_unit_sup_normalized

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (hfc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfsup : sSup (Set.range f) = 1)
    (hgsup : sSup (Set.range g) = 1) :
    ENNReal.ofReal (1 - l) * (∫⁻ x, f x) +
        ENNReal.ofReal l * (∫⁻ x, g x) ≤
      ∫⁻ z, sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
        (1 - l) • x + l • y = z ∧
          q = f x ^ (1 - l) * g y ^ l} := by
  apply ConvexOptimization.leindler_additive_lower_integral_real_line_unit_sup_normalized
    l hl0 hl1 f g
    (fun z => sSup {q : ℝ≥0∞ | ∃ x y : ℝ,
      (1 - l) • x + l • y = z ∧
        q = f x ^ (1 - l) * g y ^ l})
    hf hg hfc hgc hf1 hg1 hfsup hgsup
  intro x y
  apply le_sSup
  exact ⟨x, y, rfl, rfl⟩
