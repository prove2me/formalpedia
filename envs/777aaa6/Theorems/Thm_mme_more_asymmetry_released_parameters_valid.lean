-- Prove2me | Theorems.Thm_mme_more_asymmetry_released_parameters_valid
-- name    : mme_more_asymmetry_released_parameters_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T14:42:49.447562+00:00
-- url     : https://prove2.me/theorems/c585a841-9a5a-4197-8018-0a4460138bac
-- title:
--   The released More Asymmetry parameter data are well-formed distributions
-- statement:
--   The released More Asymmetry q = 5 fourth-power parameter data are well formed: there are 45 level-3 shapes, 6 global-region distributions, 126 positive level-3 terms and 144 zero-coordinate level-3 terms; every global distribution has 45 entries summing to the common denominator 10^15; every positive level-3 term has six region proportions summing to 10^15 and, in each region, a split distribution with one entry per admissible split summing to 10^15; every zero-coordinate complete split distribution sums to 10^15; and every level-2 split parameter is at most one half.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3, Section 7; data osf.io/mw5ak (W1.00_2.371339.mat).

import Definitions.Def_mme_more_asymmetry_released_parameters_data
open MME.MoreAsymmetryReleased
set_option autoImplicit false

theorem mme_more_asymmetry_released_parameters_valid :
    globalShapes.length = 45 ∧ globalDist.length = 6 ∧ level3Terms.length = 126 ∧
    level3Zero.length = 144 ∧
    globalDist.all (fun v ↦ v.length = 45 ∧ v.sum = den) = true ∧
    level3Terms.all (fun t ↦ t.regionProp.length = 6 ∧ t.regionProp.sum = den) = true ∧
    level3Terms.all (fun t ↦ t.splitDist.length = 6 ∧
      t.splitDist.all (fun v ↦ v.length = t.splits.length ∧ v.sum = den)) = true ∧
    level3Zero.all (fun t ↦ (t.csd.map Prod.snd).sum = den) = true ∧
    level2Split0.all (fun e ↦ 2 * e.2.2.2 ≤ den) = true := by sorry
