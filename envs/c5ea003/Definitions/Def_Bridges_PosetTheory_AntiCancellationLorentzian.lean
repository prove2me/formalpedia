-- Prove2me | Definitions.Def_Bridges_PosetTheory_AntiCancellationLorentzian
-- name    : Bridges_PosetTheory_AntiCancellationLorentzian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:18.319099+00:00
-- url     : https://prove2.me/theorems/ffa54941-c44e-4df6-8cb4-7fda0adc8585
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_AntiCancellationLorentzian
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.AntiCancellationLorentzian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/AntiCancellationLorentzian.lean by skeleton subtraction
import Mathlib
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

namespace AntiCancellation

/-! ## Definitions -/

/-- A strictly positive weight matrix for a second-order differential operator. -/
structure PositiveHessianOp (σ : Type*) [Fintype σ] where
  /-- The weight function `A : σ → σ → ℝ` -/
  weight : σ → σ → ℝ
  /-- All weights are strictly positive -/
  pos : ∀ i j, 0 < weight i j



/-- The weighted Hessian operator applied to a polynomial:
    `D_A f = ∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼ f` -/
def positiveHessianApply {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : PositiveHessianOp σ) (f : MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i : σ, ∑ j : σ,
    MvPolynomial.C (A.weight i j) * MvPolynomial.pderiv i (MvPolynomial.pderiv j f)

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

/-! ## Second Shadow Reachability (propositional, clean formulation) -/

/-- An exponent `β` is in the second shadow of a set `S` (propositional version)
    if there exists `α ∈ S` and coordinates `i, j` such that `α = β + eᵢ + eⱼ`.
    This avoids truncating subtraction and gives a clean additive characterization. -/
def InSecondShadow {σ : Type*} [DecidableEq σ]
    (S : Set (σ →₀ ℕ)) (β : σ →₀ ℕ) : Prop :=
  ∃ α ∈ S, ∃ i j : σ, α = β + Finsupp.single i 1 + Finsupp.single j 1

/-! ## Cross-Domain Theorem: Support Monotonicity -/

/-
**Cross-Domain Theorem (Support Monotonicity under Positive Hessian).**
    For any polynomial `f` with nonneg coefficients and any strictly positive
    weight matrix `A`, every exponent in the second shadow of `supp(f)` has
    nonzero (in fact, strictly positive) coefficient in `D_A f`.

    This bridges:
    - **Discrete convex analysis**: second shadow as combinatorial operation on supports
    - **Elliptic operator theory**: positive Hessian as discrete elliptic operator
    - **Symbolic computation**: certified support propagation for differential operators

    It says: positive elliptic symbols induce monotone support propagation.
-/

end AntiCancellation


