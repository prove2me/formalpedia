-- Prove2me | Theorems.Thm_EMLFixedPoint_no_fixedPoint_log_two_half
-- name    : EMLFixedPoint.no_fixedPoint_log_two_half
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:43.375694+00:00
-- url     : https://prove2.me/theorems/c25cc500-1c9e-4dae-8e40-f1c512902cfc
-- title:
--   A tangent-line estimate showing that the proposed test case can fail.
-- statement:
--   A tangent-line estimate showing that the proposed test case can fail.
--
--   ```lean
--   theorem EMLFixedPoint.no_fixedPoint_log_two_half{x : ℝ} (hdomain : 0 < x + (1 / 2 : ℝ)) :
--       emlMap (Real.log 2) (1 / 2) x ≠ x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/FixedPointIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/FixedPointIteration.lean#L121

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

theorem EMLFixedPoint.no_fixedPoint_log_two_half{x : ℝ} (hdomain : 0 < x + (1 / 2 : ℝ)) :
    emlMap (Real.log 2) (1 / 2) x ≠ x := by sorry
