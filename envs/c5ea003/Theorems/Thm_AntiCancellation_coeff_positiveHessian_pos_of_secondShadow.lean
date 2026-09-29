-- Prove2me | Theorems.Thm_AntiCancellation_coeff_positiveHessian_pos_of_secondShadow
-- name    : AntiCancellation.coeff_positiveHessian_pos_of_secondShadow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:58.507416+00:00
-- url     : https://prove2.me/theorems/dd49df72-7469-450d-89e9-ed5a3590f86e
-- title:
--   Coeff positiveHessian pos of secondShadow
-- statement:
--   Formal statement of `AntiCancellation.coeff_positiveHessian_pos_of_secondShadow` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AntiCancellation.coeff_positiveHessian_pos_of_secondShadow{σ : Type*} [DecidableEq σ] [Fintype σ]
--       (A : PositiveHessianOp σ) (f : MvPolynomial σ ℝ)
--       (hnonneg : ∀ α, 0 ≤ MvPolynomial.coeff α f) (β : σ →₀ ℕ)
--       (hreach : ∃ i j : σ, 0 < MvPolynomial.coeff (β + Finsupp.single i 1 + Finsupp.single j 1) f) :
--       0 < MvPolynomial.coeff β (positiveHessianApply A f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/AntiCancellationLorentzian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/AntiCancellationLorentzian.lean#L217

-- Thm stub generated from Bridges/PosetTheory/AntiCancellationLorentzian.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_AntiCancellationLorentzian
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Anti-Cancellation for Aggregated Derivatives of Lorentzian Polynomials

This file formalizes the **anti-cancellation principle** for second-order differential
operators applied to multivariate polynomials with nonneg coefficients. The core discovery
is that positive aggregation of second derivatives cannot erase reachable second-shadow
exponents: if `β` is reachable from the support of `f` via subtraction of `eᵢ + eⱼ`,
and `f` has nonneg coefficients, then the coefficient of `β` in `D_A f = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f`
is strictly positive whenever `A` is a strictly positive weight matrix.

## Main Definitions

* `SecondShadow` — The second shadow of a support set: all `β` reachable by subtracting
  `eᵢ + eⱼ` from some support element
* `DiagSecondShadow` — The diagonal second shadow: reachable by subtracting `2eᵢ`
* `PositiveHessianOp` — A strictly positive weight matrix for the Hessian operator
* `positiveHessianApply` — The weighted Hessian operator `D_A f = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f`

## Main Results

* `coeff_pderiv_pderiv_eq` — Explicit coefficient formula for `∂ᵢ∂ⱼ f` at exponent `β`
* `coeff_diagTrace_eq` — Coefficient formula for the diagonal trace `∑ᵢ ∂ᵢ² f`
* `coeff_diagTrace_nonneg` — Nonnegativity of the diagonal trace coefficient
* `coeff_diagTrace_pos_of_diagReachable` — **Theorem A**: Diagonal anti-cancellation
* `coeff_positiveHessian_pos_of_secondShadow` — **Theorem C**: Full weighted Hessian
  anti-cancellation under strictly positive weights
* `secondShadow_subset_support_positiveHessian` — **Cross-domain theorem**: Support
  monotonicity — the second shadow maps into the support of any positive Hessian operator

## Scientific Significance

This establishes a new structural bridge between:
- **Discrete convex analysis**: M-convex exchange and support combinatorics
- **Hodge/Lorentzian positivity**: coefficient sign constraints from Lorentzian structure
- **Elliptic operator theory**: positive second-order operators preserve observable modes
- **Symbolic computation**: certified sparsity propagation for differential operators

The key meta-discovery is that Lorentzianity is not required for the raw anti-cancellation
theorem — coefficient nonnegativity alone suffices. Lorentzianity becomes significant as the
natural structural source guaranteeing these coefficient/sign hypotheses.

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open MvPolynomial Finsupp BigOperators

noncomputable section

open AntiCancellation

/-! ## Definitions -/





/-! ## Coefficient Formulas for Second Derivatives -/

/-
The coefficient of `β` in `∂ᵢ(∂ⱼ f)` equals
    `(β(j) + 1 + if i = j then 1 else 0) * (β(i) + 1) * coeff (β + eᵢ + eⱼ) f`
    when `i ≠ j`, and `(β(i) + 1)(β(i) + 2) * coeff (β + 2eᵢ) f` when `i = j`.
-/


/-! ## Diagonal Trace Coefficient Formula -/

/-
The coefficient of `β` in the diagonal trace `∑ᵢ ∂ᵢ² f` equals the sum
    over all `i` of `(β(i)+1)(β(i)+2) * coeff(β + 2eᵢ) f`.
-/

/-! ## Anti-Cancellation Theorems -/

/-
Each summand in the diagonal trace is nonneg when `f` has nonneg coefficients.
-/

/-
The coefficient of `β` in the diagonal trace is nonneg when `f` has nonneg
    coefficients.
-/

/-
**Theorem A (Diagonal Anti-Cancellation).**
    If `f` has nonneg coefficients and `β` is diagonally reachable from the support
    (i.e., there exists `α ∈ supp(f)` and `i` with `α = β + 2eᵢ` and `coeff α f > 0`),
    then the coefficient of `β` in the diagonal trace `∑ᵢ ∂ᵢ² f` is strictly positive.
-/

/-
**Theorem B (Weighted Hessian Coefficient Formula).**
    The coefficient of `β` in the positive weighted Hessian `D_A f = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f`
    is a nonneg linear combination of coefficients of `f` when `f` has nonneg coefficients
    and `A` has positive weights. Each summand `Aᵢⱼ * cᵢⱼ(β) * coeff(β+eᵢ+eⱼ) f ≥ 0`.
-/

/-
**Theorem C (Positive Weighted Hessian Anti-Cancellation).**
    If `f` has nonneg coefficients, `A` is a strictly positive weight matrix,
    and `β` is reachable from the support via the second shadow (i.e., there exist
    `i, j` with `coeff(β + eᵢ + eⱼ) f > 0`), then the coefficient of `β` in
    `D_A f` is strictly positive.

    This is the main anti-cancellation theorem. It shows that positive aggregation
    of second derivatives cannot erase reachable exponents.
-/

theorem AntiCancellation.coeff_positiveHessian_pos_of_secondShadow{σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : PositiveHessianOp σ) (f : MvPolynomial σ ℝ)
    (hnonneg : ∀ α, 0 ≤ MvPolynomial.coeff α f) (β : σ →₀ ℕ)
    (hreach : ∃ i j : σ, 0 < MvPolynomial.coeff (β + Finsupp.single i 1 + Finsupp.single j 1) f) :
    0 < MvPolynomial.coeff β (positiveHessianApply A f) := by sorry
