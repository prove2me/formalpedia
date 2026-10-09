-- Prove2me | Theorems.Thm_d9_left_derivative_nonneg_of_eventual_max
-- name    : d9_left_derivative_nonneg_of_eventual_max
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:43:14.853871+00:00
-- url     : https://prove2.me/theorems/20425ae3-283d-4fd9-ba31-eeafd2fa12ef
-- title:
--   Left derivative at an eventual local maximum
-- statement:
--   If a function has a left derivative at a point and is eventually bounded above by its value there to the left, that derivative is nonnegative.
-- source:
--   Cause-linked repair of failed extracted publication b51999bd-b179-4116-bcf0-4abe5f223c98; exact source declaration 119, restoring the scoped topology filter notation required by its statement.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem d9_left_derivative_nonneg_of_eventual_max
    (g : ℝ → ℝ) (p lval : ℝ)
    (hderiv : HasDerivWithinAt g lval (Set.Iic p) p)
    (hmax : ∀ᶠ u in 𝓝[Set.Iic p \ {p}] p, g u ≤ g p) :
    0 ≤ lval := by sorry
