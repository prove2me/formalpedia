-- Prove2me | Theorems.Thm_Hirsch_additive_portal_repair_polynomial_route
-- name    : Hirsch.additive_portal_repair_polynomial_route
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T23:50:36.49352+00:00
-- url     : https://prove2.me/theorems/32dbbfe9-bd4c-4685-8df6-7a4403175ef4
-- title:
--   Bounded additive sibling spill gives a polynomial actual route bound
-- statement:
--   A finite additive repair certificate assembles actual steps of a relation R.
--   A leaf has excess e<=b and an actual route of cost<=C*e. A nonleaf records one
--   initial R-edge or stationary step, followed by child repairs. Child dimensions
--   strictly drop, each child excess is at most the parent e, and sibling excesses
--   sum to at most e+b. Internal parents have positive dimension and e>b.
--   Then the certificate gives an actual route of its recorded cost, and that cost
--   is at most C*e+(1+b*C)*h*max(e-b,0). Fixed b and C give a quadratic bound.
--   The certificate is a conditional interface: dimension/excess tags are not
--   automatically geometric, and arbitrary polytopes are not asserted to admit it.
--   The cyclic fixed-slack obstruction and its adaptive routes are separate work.
-- source:
--   Explicit conditional recurrence and actual-route assembly; https://github.com/jjoshua2/prove2me-work/tree/b7a832e9ff98743d53c66d6e471fd0828891d22d

import Mathlib
import Definitions.Def_Hirsch_additive_portal_repair
open scoped BigOperators
open HirschRegionRoute HirschAdditiveAllowance

theorem Hirsch.additive_portal_repair_polynomial_route {V : Type*} {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : HirschAdditiveAllowance.AdditiveRepair R b C x y h e cost) :
    HirschRegionRoute.Route R cost x y ∧ cost ≤ C*e+(1+b*C)*h*(e-b) := by sorry
