-- Prove2me | Theorems.Thm_ReweightedNPMLE_absolutelyContinuous_finiteProduct
-- name    : ReweightedNPMLE.absolutelyContinuous_finiteProduct
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:07.109298+00:00
-- url     : https://prove2.me/theorems/a8fe21f4-5b59-4d84-9f16-272711890287
-- title:
--   Absolute continuity of finite homogeneous product measures
-- statement:
--   Let $\mu$ and $\nu$ be sigma-finite measures on the same measurable space and assume $\mu\ll\nu$. For every finite $n\in\mathbb N$,
--   $$\mu^{\otimes n}\ll\nu^{\otimes n}.$$
--   Thus every set of $n$-tuples having zero measure under the reference product law also has zero measure under the product law of $\mu$. The statement includes the empty product when $n=0$. It applies, for example, when a conull geometric property established under Lebesgue product measure must be transferred to an iid sample law with a density.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ConditionalProductBound.lean#L63-L82

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

theorem ReweightedNPMLE.absolutelyContinuous_finiteProduct {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν] (h : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n ↦ μ) ≪ Measure.pi (fun _ : Fin n ↦ ν) := by sorry
