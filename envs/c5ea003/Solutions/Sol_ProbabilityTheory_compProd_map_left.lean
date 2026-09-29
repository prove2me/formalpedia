-- Prove2me | solution 1 for ProbabilityTheory.compProd_map_left
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T16:47:55.96916+00:00
-- url     : https://prove2.me/submissions/588cdbed-81d3-4d43-b664-e7ce95e47fbb

import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Relabelling the first coordinate of a composition-product

`(μ.map ι) ⊗ₘ η = (μ ⊗ₘ (η.comap ι hι)).map (Prod.map ι id)`.

Pushing the first marginal forward along `ι` and then composing with a kernel `η` is the same as
composing with the pulled-back kernel first and relabelling afterwards.

This is the transport needed to move a composition-product between two indexings of the same
space — for instance between histories indexed by `Fin n` and by an initial segment `Iic (n-1)`,
which is how the finite-horizon and infinite-horizon canonical models are related.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem solution {α α' β : Type*} {mα : MeasurableSpace α} {mα' : MeasurableSpace α'}
    {mβ : MeasurableSpace β} (μ : Measure α) [SFinite μ]
    {ι : α → α'} (hι : Measurable ι) (η : Kernel α' β) [IsSFiniteKernel η] :
    (μ.map ι) ⊗ₘ η = (μ ⊗ₘ (η.comap ι hι)).map (Prod.map ι id) := by
  have hmap : Measurable (Prod.map ι (id : β → β)) := hι.prodMap measurable_id
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hmap hs),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hι]
  refine lintegral_congr fun y ↦ ?_
  rw [Kernel.comap_apply]
  congr 1
