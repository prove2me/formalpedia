-- Prove2me | Theorems.Thm_chordal_metric_identity
-- name    : chordal_metric_identity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:32.365811+00:00
-- url     : https://prove2.me/theorems/8c8da88e-918c-42eb-bd69-72a91e24c2c6
-- title:
--   Chordal metric identity.
-- statement:
--   **Chordal metric identity.**  For the inverse stereographic projection into
--   the Euclidean product `WithLp 2 (E × ℝ)`,
--   `‖invStereo x - invStereo y‖² = 4‖x - y‖² / ((1 + ‖x‖²)(1 + ‖y‖²))`.
--
--   ```lean
--   theorem chordal_metric_identity(x y : E) :
--       ‖invStereo x - invStereo y‖ ^ 2
--         = 4 * ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NumberTheory/ChordalMetricIdentity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NumberTheory/ChordalMetricIdentity.lean#L50

-- Thm stub generated from Applications/NumberTheory/ChordalMetricIdentity.lean
import Mathlib
import Definitions.Def_Applications_NumberTheory_ChordalMetricIdentity
/-
Copyright (c) 2024 Harmonic Research. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The chordal metric identity for inverse stereographic projection

Let `E` be a real inner product space.  The **inverse stereographic projection**
sends a point `x ∈ E` to a point on the unit sphere of `E × ℝ`:

  `invStereo x = (2x / (1 + ‖x‖²), (‖x‖² - 1) / (1 + ‖x‖²))`.

To measure distances on the sphere with the Euclidean (`L²`) metric we take the
codomain to be `WithLp 2 (E × ℝ)`, whose squared norm decomposes as
`‖(u, t)‖² = ‖u‖² + t²` (`WithLp.prod_norm_sq_eq_of_L2`).

The main result `chordal_metric_identity` is the global **chordal metric
identity**

  `‖invStereo x - invStereo y‖² = 4‖x - y‖² / ((1 + ‖x‖²)(1 + ‖y‖²))`.

Infinitesimally this recovers the conformal factor of stereographic projection:
`ds²_sphere = 4/(1 + ‖x‖²)² · ds²_flat`.

## Proof outline

Writing `a = ‖x‖²`, `b = ‖y‖²`, `s = ⟪x, y⟫`, we expand the squared distance in
`WithLp 2 (E × ℝ)` into a horizontal part
`‖(2/(1+a)) • x - (2/(1+b)) • y‖²` and a vertical part
`((a-1)/(1+a) - (b-1)/(1+b))²`.  The horizontal part is expanded with the
polarisation identity `norm_sub_sq_real` together with `norm_smul` and the
bilinearity of the real inner product, and `‖x - y‖²` on the right-hand side is
likewise expanded.  What remains is a rational-function identity in `a, b, s`
over the positive denominators `1 + a`, `1 + b`, which `field_simp` and `ring`
discharge.
-/

open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem chordal_metric_identity(x y : E) :
    ‖invStereo x - invStereo y‖ ^ 2
      = 4 * ‖x - y‖ ^ 2 / ((1 + ‖x‖ ^ 2) * (1 + ‖y‖ ^ 2)) := by sorry
