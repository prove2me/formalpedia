-- Prove2me | Definitions.Def_Bridges_CertifiedRadiusResiduated
-- name    : Bridges_CertifiedRadiusResiduated
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:04.310187+00:00
-- url     : https://prove2.me/theorems/48b4c107-7e4b-4bd2-933a-7b742c71fd58
-- title:
--   Aether Catalog definitions — Bridges_CertifiedRadiusResiduated
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CertifiedRadiusResiduated`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CertifiedRadiusResiduated.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Certified Radii as Residuated Tropical Invariants

This file establishes a formal bridge between certified robustness radii,
residuated/order-theoretic algebra on `WithBot ℝ`, and computable benchmark
certification. The key insight is that a certified radius is not merely an
analytic estimate, but an **order-theoretic residual**: the largest perturbation
budget compatible with a margin inequality.

## Main Definitions

* `certifiedRadius` — The canonical scalar certified radius `max(0, m/K)`
* `residualReal` — The real-valued residual operation `b - a`
* `wbotResidual` — Residual operation on `WithBot ℝ`

## Main Results

### Monotonicity (Theorem A)
* `certifiedRadius_mono` — Monotonicity under margin increase and Lipschitz decrease
* `certifiedRadius_monotone_margin` — Monotone in margin for fixed Lipschitz
* `certifiedRadius_antitone_Lipschitz` — Antitone in Lipschitz for fixed margin

### Residuation (Theorem B)
* `real_add_le_iff_le_sub` — Adjunction law for reals: `a + r ≤ b ↔ r ≤ b - a`
* `withBot_coe_le_iff` — Coercion preserves order on `WithBot ℝ`
* `wbotResidual_adjoint_coe` — Residual adjunction for coerced reals in `WithBot ℝ`

### Benchmarking (Theorem C)
* `finite_certified_ball_nonneg` — Finite benchmark certificate theorem

### Cross-Domain
* `certifiedRadius_residual_connection` — Certified radius as a residual witness

## References

- Builds on `certified_residuated_bound` from `TropicalKernelMeanDuality.lean`
- Extends patterns from `certified_entropy_extraction_Lipschitz_bound`
- Connects to `tropical_lattice_det_bound` for geometric certificate mechanisms
-/

noncomputable section

open Finset BigOperators

/-! ## §1. Certified Radius Definition -/

/-- The canonical scalar certified radius: the maximum perturbation radius guaranteed
    by a margin `m` and Lipschitz constant `K`. When `m ≤ 0`, the radius is 0;
    when `K ≤ 0`, the division is degenerate and clamped to 0. -/
def certifiedRadius (m K : ℝ) : ℝ := max 0 (m / K)

/-- The real-valued residual operation, forming the right adjoint of addition:
    `a + r ≤ b ↔ r ≤ residualReal a b`. -/
def residualReal (a b : ℝ) : ℝ := b - a

/-! ## §2. Theorem A — Monotonicity of Certified Radius -/

/-
**Certified radius is monotone in margin** for fixed positive Lipschitz constant.
    Increasing the classification margin can only increase the certified perturbation radius.
-/

/-
**Certified radius is antitone in Lipschitz constant** for fixed margin.
    A smaller Lipschitz constant yields a larger certified radius.
-/

/-
**Combined monotonicity**: increasing margin and decreasing Lipschitz constant
    both increase the certified radius. This is the fundamental order-theoretic
    compositionality law for robustness certificates.
-/

/-! ## §3. Theorem B — Residuation on Reals and `WithBot ℝ` -/

/-
**Adjunction law for reals**: the fundamental identity that makes subtraction
    the right adjoint (residual) of addition in the ordered group `(ℝ, +, ≤)`.
    This is the algebraic seed from which all residuated lattice structure grows.
-/

/-
Coercion from `ℝ` to `WithBot ℝ` preserves and reflects order.
-/

/-
Coercion from `ℝ` to `WithBot ℝ` preserves addition.
-/

/-
**Residual adjunction for coerced reals in `WithBot ℝ`**:
    For real values `a`, `b`, `r` lifted to `WithBot ℝ`, the addition-residual
    adjunction holds: `↑(a + r) ≤ ↑b ↔ ↑r ≤ ↑(b - a)`.

    This is the first step toward full residuated lattice structure on `WithBot ℝ`,
    restricted to the well-behaved fragment of actual real values.
-/

/-- The `WithBot ℝ`-valued residual operation. For two `WithBot ℝ` values,
    this computes the greatest `r` such that `a + r ≤ b`, with `⊥` behavior:
    - `wbotResidual ⊥ b = ⊤` conceptually, but we use `⊥` as safe fallback
    - `wbotResidual a ⊥ = ⊥` -/
def wbotResidual (a b : WithBot ℝ) : WithBot ℝ :=
  match a, b with
  | ⊥, _ => ⊥      -- conservative: ⊥ + anything = ⊥, so any r works; use ⊥ as safe default
  | _, ⊥ => ⊥       -- ⊥ is below everything, so a + r ≤ ⊥ only if a + r = ⊥
  | some a', some b' => (b' - a' : ℝ)

/-
The residual operation on coerced reals agrees with real subtraction.
-/

/-! ## §4. Theorem C — Finite Benchmark Certificate -/

/-
**Finite certified ball nonnegativity**: Given a function `f` with margin `m` at
    center `x`, Lipschitz constant `K` over a finite set `S`, and radius `r` within
    the certified radius, every point in `S` within distance `r` of `x` has `f(y) ≥ 0`.

    This theorem turns abstract Lipschitz certification into executable benchmarking:
    it suffices to check the margin and Lipschitz condition at finitely many points,
    and the radius certificate automatically guarantees nonnegativity within the ball.
-/

/-! ## §5. Cross-Domain Connections -/

/-
**Certified radius as a residual witness**: the certified radius `max(0, m/K)`
    is exactly the largest nonneg real `r` such that `K * r ≤ m`, when `K > 0`.
    This connects the analytic certified radius to the residual interpretation:
    the radius is the residual of `K` in `m` under multiplication, clamped to `[0, ∞)`.
-/

/-
**Tropical max interpretation**: The certified radius operation `max(0, m/K)`
    is a tropical (max-plus) expression: it is the max of the additive identity 0
    and the quotient m/K. This places certified radii within tropical algebra.
-/

/-
Nonneg certified radius: the certified radius is always nonnegative.
-/

/-
The certified radius is zero when the margin is nonpositive and K > 0.
-/

/-
The certified radius satisfies the fundamental margin inequality:
    `K * certifiedRadius m K ≤ m` when `m ≥ 0` and `K > 0`.
-/

end


