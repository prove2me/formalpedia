-- Prove2me | Theorems.Thm_mme_regional_ambient_entropy_bound
-- name    : mme_regional_ambient_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T21:16:29.967261+00:00
-- url     : https://prove2.me/theorems/fed8e0b0-b14f-4b44-9378-0f444b7ae202
-- title:
--   The actual ambient competitor count obeys the maximum-entropy rate
-- statement:
--   Bound the actual ambient family by the exponential of joint entropy plus the existing maximum-entropy penalty, with a constructed polynomial count of all integer types. Also derive nonnegativity of the regional penalty.
-- source:
--   The More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Uniform bounds for the actual common hash construction; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem mme_regional_ambient_entropy_bound {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, Split half (parent r) → ℕ) (hm : ∀ r, ∑ c, m r c = n r) :
    0 ≤ penaltyPotential n m ∧
    ((ambient (n := n) m).card : ℝ) ≤
      ((((∑ r, n r : ℕ) : ℝ) + 1)) ^ Fintype.card (MME.RecursiveYZ.Cell half R parent) *
        Real.exp (jointPotential m + penaltyPotential n m) := by sorry
