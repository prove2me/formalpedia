-- Prove2me | Theorems.Thm_AntiCancellation_coeff_pderiv_pderiv_ne
-- name    : AntiCancellation.coeff_pderiv_pderiv_ne
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:58.391669+00:00
-- url     : https://prove2.me/theorems/017b586e-541e-49d0-9180-c63a0c8315e8
-- title:
--   Coeff pderiv pderiv ne
-- statement:
--   Formal statement of `AntiCancellation.coeff_pderiv_pderiv_ne` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AntiCancellation.coeff_pderiv_pderiv_ne{σ : Type*} [DecidableEq σ]
--       (f : MvPolynomial σ ℝ) (i j : σ) (hij : i ≠ j) (β : σ →₀ ℕ) :
--       MvPolynomial.coeff β (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) =
--       (↑(β i + 1) : ℝ) * (↑(β j + 1) : ℝ) *
--         MvPolynomial.coeff (β + Finsupp.single i 1 + Finsupp.single j 1) f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/AntiCancellationLorentzian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/AntiCancellationLorentzian.lean#L99

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

theorem AntiCancellation.coeff_pderiv_pderiv_ne{σ : Type*} [DecidableEq σ]
    (f : MvPolynomial σ ℝ) (i j : σ) (hij : i ≠ j) (β : σ →₀ ℕ) :
    MvPolynomial.coeff β (MvPolynomial.pderiv i (MvPolynomial.pderiv j f)) =
    (↑(β i + 1) : ℝ) * (↑(β j + 1) : ℝ) *
      MvPolynomial.coeff (β + Finsupp.single i 1 + Finsupp.single j 1) f := by sorry
