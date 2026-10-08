-- Prove2me | Theorems.Thm_d9_right_derivative_nonpos_of_eventual_max
-- name    : d9_right_derivative_nonpos_of_eventual_max
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:42:55.182873+00:00
-- url     : https://prove2.me/theorems/6fe41cab-c9a4-4d92-b212-40c437f4fa5e
-- title:
--   Right derivative at an eventual local maximum
-- statement:
--   If a function has a right derivative at a point and is eventually bounded above by its value there to the right, that derivative is nonpositive.
-- source:
--   Cause-linked repair of failed extracted publication 1b2b604b-905c-4deb-97e3-7bb02e68e208; exact source declaration 118, restoring the scoped topology filter notation required by its statement.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem d9_right_derivative_nonpos_of_eventual_max
    (g : ℝ → ℝ) (p r : ℝ)
    (hderiv : HasDerivWithinAt g r (Set.Ici p) p)
    (hmax : ∀ᶠ u in 𝓝[Set.Ici p \ {p}] p, g u ≤ g p) :
    r ≤ 0 := by sorry
