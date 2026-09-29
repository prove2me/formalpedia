-- Prove2me | Theorems.Thm_EMLFixedPoint_lipschitzOn_emlMap_Icc
-- name    : EMLFixedPoint.lipschitzOn_emlMap_Icc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:47:09.151691+00:00
-- url     : https://prove2.me/theorems/c3d2ddb7-1f6c-48e0-8783-331121e80967
-- title:
--   The derivative bound on a positive interval gives the expected Lipschitz bound.
-- statement:
--   The derivative bound on a positive interval gives the expected Lipschitz bound.
--
--   ```lean
--   theorem EMLFixedPoint.lipschitzOn_emlMap_Icc{a c L U q : ℝ}
--       (hpos : 0 < L + c) (hq0 : 0 ≤ q) (hderiv : Real.exp a / (L + c) ≤ q) :
--       LipschitzOnWith ⟨q, hq0⟩ (emlMap a c) (Icc L U) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/FixedPointIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/FixedPointIteration.lean#L36

-- Thm stub generated from Applications/EML/FixedPointIteration.lean
import Mathlib
import Definitions.Def_Applications_EML_FixedPointIteration

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

open EMLFixedPoint

theorem EMLFixedPoint.lipschitzOn_emlMap_Icc{a c L U q : ℝ}
    (hpos : 0 < L + c) (hq0 : 0 ≤ q) (hderiv : Real.exp a / (L + c) ≤ q) :
    LipschitzOnWith ⟨q, hq0⟩ (emlMap a c) (Icc L U) := by sorry
