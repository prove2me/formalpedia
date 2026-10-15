-- Prove2me | Theorems.Thm_mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le
-- name    : mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:48:29.415178+00:00
-- url     : https://prove2.me/theorems/b24acb88-a404-47e5-a131-b36ae4fa7836
-- title:
--   Homogeneous component of a finite product with order bounds
-- statement:
--   For a finitely supported family of factors whose `i`th selected factor has order at least `m i`, the homogeneous component of their product in the sum of the assigned degrees is the product of the corresponding homogeneous components. The empty support gives the degree-zero component of `1`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Order

open scoped BigOperators

theorem mvPowerSeries_homogeneousComponent_finsuppProd_of_order_le
    {σ ι R : Type*} [CommSemiring R]
    (g : ι → Nat → MvPowerSeries σ R)
    (m : ι →₀ Nat)
    (hg : ∀ i, m i ≤ (g i (m i)).order) :
    MvPowerSeries.homogeneousComponent m.degree (m.prod g) =
      m.prod (fun i k => MvPowerSeries.homogeneousComponent (m i) (g i (m i))) := by sorry
