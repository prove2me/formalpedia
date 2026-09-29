-- Prove2me | Theorems.Thm_MicroWeighting_microConstant_unique
-- name    : MicroWeighting.microConstant_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:58:38.778327+00:00
-- url     : https://prove2.me/theorems/4d0c047b-27b5-49ce-9dd0-c38694588591
-- title:
--   For a symmetric distance matrix the constant `λ` is independent of the
-- statement:
--   For a **symmetric** distance matrix the constant `λ` is independent of the
--   chosen weighting: any two microscopic weightings share the same constant.
--   This is the microscopic analogue of the well-definedness of magnitude.
--
--   ```lean
--   theorem MicroWeighting.microConstant_unique{D : Matrix n n ℝ} (hD : Dᵀ = D)
--       {w w' : n → ℝ} {a b : ℝ}
--       (hw : IsMicroWeighting D w a) (hw' : IsMicroWeighting D w' b) :
--       a = b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/MicroscopicWeighting/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/MicroscopicWeighting/Core.lean#L35

-- Thm stub generated from Applications/MicroscopicWeighting/Core.lean
import Mathlib
import Definitions.Def_Applications_MicroscopicWeighting_Core

/-!
# Microscopic weightings of finite metric spaces

In Leinster's magnitude theory a **weighting** of a finite metric space with
similarity matrix `Z_t` (entries `exp(-t·d(x_i,x_j))`) is a vector `w` with
`Z_t w = 𝟙`. As the scale `t → 0` one has `Z_t = J - t·D + O(t²)` with `J` the
all-ones matrix and `D` the **distance matrix**; a first-order analysis of
`Z_t w_t = 𝟙` shows the limiting ("microscopic") weighting `μ` satisfies

  `D μ = λ·𝟙`   and   `Σ μ = 1`

for a scalar `λ`. This file develops the elementary theory of such
*distance-matrix weightings*: the constant `λ` is well defined for symmetric `D`,
the weighting is unique when `D` is invertible, and it exists (via `D⁻¹`).

The heuristic of the research theme — that the microscopic weighting emphasises
boundary points, giving positive weight to vertices of the convex hull and
non-positive weight to interior points — is made concrete in `Examples.lean`.
-/

open MicroWeighting

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]


omit [DecidableEq n] in

theorem MicroWeighting.microConstant_unique{D : Matrix n n ℝ} (hD : Dᵀ = D)
    {w w' : n → ℝ} {a b : ℝ}
    (hw : IsMicroWeighting D w a) (hw' : IsMicroWeighting D w' b) :
    a = b := by sorry
