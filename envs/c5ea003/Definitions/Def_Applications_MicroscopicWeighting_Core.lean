-- Prove2me | Definitions.Def_Applications_MicroscopicWeighting_Core
-- name    : Applications_MicroscopicWeighting_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:34.582064+00:00
-- url     : https://prove2.me/theorems/b6694f3b-f6b8-4a6e-ac44-ff20b7d1b587
-- title:
--   Aether Catalog definitions — Applications_MicroscopicWeighting_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.MicroscopicWeighting.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/MicroscopicWeighting/Core.lean by skeleton subtraction
import Mathlib

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

namespace MicroWeighting

open Matrix BigOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `w` is a *microscopic weighting* for the distance matrix `D` with constant
`lam` if `D *ᵥ w` is the constant vector `lam` and the entries of `w` sum to `1`.
This is the leading-order (`t → 0`) form of a magnitude weighting. -/
def IsMicroWeighting (D : Matrix n n ℝ) (w : n → ℝ) (lam : ℝ) : Prop :=
  D *ᵥ w = (fun _ => lam) ∧ ∑ i, w i = 1





end MicroWeighting


