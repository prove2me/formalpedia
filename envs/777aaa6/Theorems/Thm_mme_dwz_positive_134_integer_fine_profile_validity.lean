-- Prove2me | Theorems.Thm_mme_dwz_positive_134_integer_fine_profile_validity
-- name    : mme_dwz_positive_134_integer_fine_profile_validity
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-20T19:46:52.510619+00:00
-- url     : https://prove2.me/theorems/f019b92f-18e7-4ed2-8e5e-071f8494f150
-- title:
--   The concrete DWZ (1,3,4) fine profiles are valid and preserve the released parent profile
-- statement:
--   For the explicit six-region integer fine profiles of the $(1,3,4)$ candidate, the joint coarse counts sum to each region length. Every mode has the required fine-count total in each cell; every word with positive count has the prescribed grade; and all three CW boundary complementary-profile identities hold.
--
--   The retained original Z coordinate in each physical orientation has exactly the published regional profile. Summing with the released weights recovers twice the published object-151 parent profile, the factor two accounting for the paired X/Y orientations. All region lengths are positive and their sum is the stated total count.
--
--   These facts validate the concrete integer input to the regional extraction construction. They do not assert an entropy inequality, child tensor value, or final component value.
-- source:
--   Direct verification of mme_dwz_positive_134_integer_fine_profile_data and the original object-151 profile at https://prove2.me/theorems/eca4895a-f787-4924-af5a-7e6f4fdc35ac .

import Definitions.Def_mme_dwz_positive_134_integer_fine_profile_data
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators MME MME.RecursiveYZ MME.DWZ134Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

theorem mme_dwz_positive_134_integer_fine_profile_validity :
    (∀ r, (∑ c, m r c) = n r) ∧
    (∀ i c, (∑ w, mu i c w) = m c.1 c.2 + m c.1 (complement (parent_total c.1) c.2)) ∧
    (∀ i c w, 0 < mu i c w → ∑ a, (w a).val = (c.2.val i).val) ∧
    BoundaryProfiles mu ∧
    (∀ r g, (∑ c : RecursiveThinSplit.Split 4 (parent r), if c.val (keptMode r) = g then m r c else 0) =
      weightCount r * (DWZPositiveComponent134.regionalProfile (region r)).count g * denominator) ∧
    (∀ g, (∑ r, weightCount r * (DWZPositiveComponent134.regionalProfile (region r)).count g) =
      2 * DWZPositiveComponent134.parentProfile.count g) ∧
    (∀ r, 0 < n r) ∧ (∑ r, n r) = totalCount := by sorry
