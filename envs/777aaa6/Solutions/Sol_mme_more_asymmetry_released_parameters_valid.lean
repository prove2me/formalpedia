-- Prove2me | solution 1 for mme_more_asymmetry_released_parameters_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T14:42:51.759242+00:00
-- url     : https://prove2.me/submissions/5668aefa-3f20-41f0-b74b-63a9916a53e6

import Definitions.Def_mme_more_asymmetry_released_parameters_data
open MME.MoreAsymmetryReleased
set_option autoImplicit false
set_option maxRecDepth 100000

theorem solution :
    globalShapes.length = 45 ∧ globalDist.length = 6 ∧ level3Terms.length = 126 ∧
    level3Zero.length = 144 ∧
    globalDist.all (fun v ↦ v.length = 45 ∧ v.sum = den) = true ∧
    level3Terms.all (fun t ↦ t.regionProp.length = 6 ∧ t.regionProp.sum = den) = true ∧
    level3Terms.all (fun t ↦ t.splitDist.length = 6 ∧
      t.splitDist.all (fun v ↦ v.length = t.splits.length ∧ v.sum = den)) = true ∧
    level3Zero.all (fun t ↦ (t.csd.map Prod.snd).sum = den) = true ∧
    level2Split0.all (fun e ↦ 2 * e.2.2.2 ≤ den) = true := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩
