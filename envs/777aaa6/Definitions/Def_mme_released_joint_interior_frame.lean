-- Prove2me | Definitions.Def_mme_released_joint_interior_frame
-- name    : mme_released_joint_interior_frame
-- status  : Definition
-- author  : @Robertboy18
-- created : 2026-09-23T09:43:28.109962+00:00
-- url     : https://prove2.me/theorems/8bcbc67f-e01e-4bd0-ad82-deb2f4e5b904
-- title:
--   The common parent-typical source window
-- statement:
--   Physical positions and the common parent-typical source predicate for a joint released inner region. This defines the window; its connection to the outer extraction remains a separate obligation.

import Definitions.Def_mme_released_joint_interior_profiles
import Definitions.Def_mme_recursive_profiled_CW_data

open scoped BigOperators

namespace MME.ReleasedJointInterior

/-- Number of fourth-power parent components in one common inner region. -/
def blocks (r : Fin 6) (k : ℕ) : ℕ := ∑ j, size r k j

/-- Flatten both square children of every parent occurrence. -/
noncomputable def positions (r : Fin 6) (k : ℕ) :
    Fin (blocks r k * 2) ≃ RecursiveYZ.Position (size r k) :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, Fintype.card_sigma, Fintype.card_prod]
    simp only [← Finset.sum_mul, blocks])

theorem positions_length (r : Fin 6) (k : ℕ) :
    (blocks r k * 2) * 2 ^ (2 - 1) = blocks r k * 4 := by omega

/-- A common parent-typical window across all owners and parent shapes.
The marginal constraints keep the owner and shape labels separate. -/
noncomputable def source (r : Fin 6) (k : ℕ) (epsilon : ℝ) :
    ProfiledCW.Predicate (blocks r k * 4) :=
  fun i x => RegionRealization.parentTypical (parent_total r) (size r k)
    (splitCount r k) (integerProfile r k i) epsilon
    (ProfiledCW.split (ell := 2) (positions r k) (positions_length r k) x)

end MME.ReleasedJointInterior


