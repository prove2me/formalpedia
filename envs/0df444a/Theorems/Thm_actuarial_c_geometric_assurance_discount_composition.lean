-- Prove2me | Theorems.Thm_actuarial_c_geometric_assurance_discount_composition
-- name    : actuarial_c_geometric_assurance_discount_composition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:38:45.188015+00:00
-- url     : https://prove2.me/theorems/5fb1914a-eb87-4550-b591-a3c91ab2d652
-- title:
--   Geometrically escalating death sums assured compose exactly with year-end discounting
-- statement:
--   For a death-year lump-sum schedule growing geometrically at rate g, the realised end-of-year death-claim EPV is v times the death-year probability generating polynomial evaluated at vg. This gives the otherwise isolated geometric benefit schedule a genuine actuarial valuation role. The result remains unproved.
-- source:
--   Original derived geometric-death-assurance identity informed by Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 5; https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. Not a verbatim published Lean theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_geom

open ActuarialAssurances

theorem actuarial_c_geometric_assurance_discount_composition
    (h : ℕ) (v g : ℝ) (p : ℕ → ℝ) :
    epv h v (geom g) p =
      v * (∑ j ∈ Finset.range h, (v*g)^j * p j) := by sorry
