-- Prove2me | Definitions.Def_Applications_EML_FixedPointIteration
-- name    : Applications_EML_FixedPointIteration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:43.443419+00:00
-- url     : https://prove2.me/theorems/38ec6ed8-2d19-4fe9-be99-d58775a709f7
-- title:
--   Aether Catalog definitions — Applications_EML_FixedPointIteration
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EML.FixedPointIteration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EML/FixedPointIteration.lean by skeleton subtraction
import Mathlib

/-!
# Fixed points of an exponential--logarithmic iteration

This file studies `x ↦ exp a * log (x + c)`.  The unrestricted test claim from
this research question is false: even with `0 < a < 1` and `0 < c < 1`, a fixed
point need not exist.  We prove this for `a = log 2`, `c = 1/2` on the natural
logarithmic domain.

The positive result is the precise contraction theorem suggested by the question.
On a closed invariant interval `[L,U]`, if `L+c>0` and
`exp a / (L+c) ≤ q < 1`, the map has a unique fixed point in the interval;
every iteration starting there converges to it with Banach's geometric error bound.
-/

noncomputable section

open Real Set Filter Function Topology

namespace EMLFixedPoint

/-- The EML exponential--logarithmic update with `b = 1`. -/
def emlMap (a c : ℝ) (x : ℝ) : ℝ :=
  Real.exp a * Real.log (x + c)



/-- Restriction of an invariant EML update to its interval. -/
def restrictedMap {a c L U : ℝ} (hmap : MapsTo (emlMap a c) (Icc L U) (Icc L U)) :
    Icc L U → Icc L U := hmap.restrict (emlMap a c) (Icc L U) (Icc L U)






end EMLFixedPoint


