-- Prove2me | solution 1 for ReweightedNPMLE.absolutelyContinuous_finiteProduct
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:52:44.376705+00:00
-- url     : https://prove2.me/submissions/b820e153-f02f-4bb7-bc0d-d194d23aa62e

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Integrating uniform conditional exceptional-event bounds

A measurable joint bad event whose sections have probability at most `eps`
off a data exceptional set has total probability at most the data failure
plus `eps`. The section bounds may come from arbitrary pointwise witnesses;
no measurable choice of those witnesses is required.
-/

open Set MeasureTheory
open scoped ENNReal
/-- Absolute continuity is preserved by a finite homogeneous product.
This transfers the simultaneous Lebesgue-conull Gaussian event to the
joint sample law. -/
theorem solution {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ μ) ≪ Measure.pi (fun _ : Fin n ↦ ν) := by
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ X) 0).symm
      have hm : ((μ.prod (Measure.pi (fun _ : Fin n ↦ μ))).map e) =
          Measure.pi (fun _ : Fin (n + 1) ↦ μ) := by
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ μ) 0).symm.map_eq
      have hn : ((ν.prod (Measure.pi (fun _ : Fin n ↦ ν))).map e) =
          Measure.pi (fun _ : Fin (n + 1) ↦ ν) := by
        exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ν) 0).symm.map_eq
      have hh := e.measurableEmbedding.absolutelyContinuous_map (h.prod ih)
      rw [hm, hn] at hh
      exact hh
