-- Prove2me | Theorems.Thm_HenonCanonicalHeight_normalized_height_error_bound
-- name    : HenonCanonicalHeight.normalized_height_error_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:23.708522+00:00
-- url     : https://prove2.me/theorems/6e9c4649-93cd-4d5c-ad0d-6dfb21c33537
-- title:
--   A finite-stage canonical-height estimate.
-- statement:
--   A finite-stage canonical-height estimate.  If a nonnegative raw height changes
--   by at most `C` from the exact degree-`D` scaling law, then every normalized iterate
--   stays within `C/(D-1)` of the initial height.  This is the geometric-series estimate
--   at the core of canonical-height constructions.
--
--   ```lean
--   theorem HenonCanonicalHeight.normalized_height_error_bound    {D : ℕ} (hD : 2 ≤ D) (h : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
--       (hscale : ∀ n, |h (n + 1) - (D : ℝ) * h n| ≤ C) :
--       ∀ n, |h n / (D : ℝ) ^ n - h 0| ≤ C / ((D : ℝ) - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HenonCanonicalHeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HenonCanonicalHeight.lean#L236

-- Thm stub generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

open HenonCanonicalHeight

theorem HenonCanonicalHeight.normalized_height_error_bound    {D : ℕ} (hD : 2 ≤ D) (h : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hscale : ∀ n, |h (n + 1) - (D : ℝ) * h n| ≤ C) :
    ∀ n, |h n / (D : ℝ) ^ n - h 0| ≤ C / ((D : ℝ) - 1) := by sorry
