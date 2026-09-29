-- Prove2me | solution 1 for Doppelganger.no_contractive_metric_of_bijective_stimulus
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T07:49:57.65361+00:00
-- url     : https://prove2.me/submissions/3309fb63-2d28-46d1-b796-0d7a899b5c0b

import Mathlib

set_option autoImplicit false

-- Exact quantified target as elaborated in the prior backend WA receipt.
-- The first pseudometric is independent of both metric structures.
theorem solution : ¬ (∀ {S I : Type}
    [pm : PseudoMetricSpace S] [MetricSpace S] [Fintype S] [Nonempty S]
    [Fintype S] [MetricSpace S]
    (δ : S → I → S) (i₀ : I), Function.Bijective (δ · i₀) →
    ∀ {k : ℝ}, 0 ≤ k → k < 1 →
    (∀ (i : I) (s t : S),
      @dist S pm.toDist (δ s i) (δ t i) ≤ k * @dist S pm.toDist s t) →
    ∀ s t : S, s = t) := by
  intro h
  let z : PseudoMetricSpace Bool :=
    PseudoMetricSpace.induced (fun _ : Bool => (0 : ℝ)) inferInstance
  let m : MetricSpace Bool := MetricSpace.induced
    (fun b : Bool => if b then (1 : ℝ) else 0)
    (by intro a b hab; cases a <;> cases b <;> norm_num at *) inferInstance
  have hcontract : ∀ (i : Unit) (s t : Bool),
      @dist Bool z.toDist s t ≤ (0 : ℝ) * @dist Bool z.toDist s t := by
    intro i s t
    change dist (0 : ℝ) 0 ≤ 0 * dist (0 : ℝ) 0
    simp
  have heq : false = true := @h Bool Unit z m inferInstance inferInstance
    inferInstance m (fun s _ => s) () Function.bijective_id
    0 (by norm_num) (by norm_num) hcontract false true
  cases heq
