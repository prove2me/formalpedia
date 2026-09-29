-- Prove2me | solution 1 for Doppelganger.exists_lock_of_contraction_finite
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-21T07:58:22.097986+00:00
-- url     : https://prove2.me/submissions/4ac4f697-38e2-4f81-bed2-fde5aef05db9

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core

set_option autoImplicit false
open Doppelganger

theorem solution : ¬ (∀ {S I : Type}
    [pm : PseudoMetricSpace S] [MetricSpace S] [Fintype S] [Nonempty S]
    (δ : S → I → S) {k : ℝ}, 0 ≤ k → k < 1 →
    (∀ (i : I) (s t : S),
      @dist S pm.toDist (δ s i) (δ t i) ≤ k * @dist S pm.toDist s t) →
    ∃ N : ℕ, ∀ w : List I, N ≤ w.length → Locks δ w) := by
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
  obtain ⟨N, hN⟩ := @h Bool Unit z m inferInstance inferInstance
    (fun s _ => s) 0 (by norm_num) (by norm_num) hcontract
  have hdrive : ∀ (w : List Unit) (s : Bool), drive (fun s _ => s) w s = s := by
    intro w
    induction w with
    | nil => intro s; rfl
    | cons i w ih => intro s; exact ih s
  have heq := hN (List.replicate N ()) (by simp) false true
  rw [hdrive, hdrive] at heq
  cases heq
