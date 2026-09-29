-- Prove2me | Theorems.Thm_mme_dwz_positive_422_integer_fine_profile_validity
-- name    : mme_dwz_positive_422_integer_fine_profile_validity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T17:57:34.859031+00:00
-- url     : https://prove2.me/theorems/d3d21a2d-5e9b-4a3a-a3f5-fbb51dda4009
-- title:
--   Positive component 422: validity of the six-region integer fine profile
-- statement:
--   For the explicit six-region integer fine profiles of the $(4,2,2)$ candidate, the joint coarse counts sum to each region length. Every mode has the required fine-count total in each cell; every word with positive count has the prescribed grade; and all three CW boundary complementary-profile identities hold.
--
--   The retained original Z coordinate in each physical orientation has exactly the published regional profile. Summing with the released weights recovers twice the published object-171 parent profile, the factor two accounting for the paired X/Y orientations. All region lengths are positive and their sum is the stated total count.
--
--   These facts validate the concrete integer input to the regional extraction construction. They do not assert an entropy inequality, child tensor value, or final component value.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7, with the regional extraction of Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6. Object-171 data generated from the released q=5 fourth-power certificate.

import Definitions.Def_mme_dwz_positive_422_integer_fine_profile_data
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators MME MME.RecursiveYZ MME.DWZ422Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

theorem mme_dwz_positive_422_integer_fine_profile_validity :
    (∀ r, (∑ c, m r c) = n r) ∧
    (∀ i c, (∑ w, mu i c w) = m c.1 c.2 + m c.1 (complement (parent_total c.1) c.2)) ∧
    (∀ i c w, 0 < mu i c w → ∑ a, (w a).val = (c.2.val i).val) ∧
    BoundaryProfiles mu ∧
    (∀ r g, (∑ c : RecursiveThinSplit.Split 4 (parent r), if c.val (keptMode r) = g then m r c else 0) =
      weightCount r * (DWZPositiveComponent422.regionalProfile (region r)).count g * denominator) ∧
    (∀ g, (∑ r, weightCount r * (DWZPositiveComponent422.regionalProfile (region r)).count g) =
      2 * DWZPositiveComponent422.parentProfile.count g) ∧
    (∀ r, 0 < n r) ∧ (∑ r, n r) = totalCount := by sorry
