-- Prove2me | Theorems.Thm_IteratedShadowGeometry_mem_kthShadow_add_iff
-- name    : IteratedShadowGeometry.mem_kthShadow_add_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:53.410601+00:00
-- url     : https://prove2.me/theorems/afaa2f5a-c645-4b5f-8bae-313a6184fc62
-- title:
--   Mem kthShadow add iff
-- statement:
--   Formal statement of `IteratedShadowGeometry.mem_kthShadow_add_iff` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem IteratedShadowGeometry.mem_kthShadow_add_iff{n : ℕ} {S : Finset (Fin n →₀ ℕ)} {a b : ℕ}
--       {β : Fin n →₀ ℕ} :
--       β ∈ kthShadow (kthShadow S a) b ↔ β ∈ kthShadow S (a + b) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/IteratedShadowGeometry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/IteratedShadowGeometry.lean#L299

-- Thm stub generated from Bridges/PosetTheory/IteratedShadowGeometry.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_IteratedShadowGeometry
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Iterated Shadow Geometry of Polynomial Supports

This file builds a theory of **iterated support shadows** for multivariate polynomials,
establishing that higher-order mixed partial differentiation has an exact combinatorial
footprint on exponent sets governed by the shadow operator on Newton supports.

## Main Definitions

* `kthShadow` — The k-th combinatorial shadow of a finite support set: all exponent
  vectors obtainable by subtracting a multi-index of total mass k from some element.
* `iteratedPDeriv` — The mixed partial derivative of a multivariate polynomial indexed
  by a multi-index τ, applying ∂ᵢ exactly τ(i) times for each variable i.
* `finsuppSupport` — The finite support of a multivariate polynomial as a Finset.
* `derivShadowProfile` — The function k ↦ |kthShadow(Supp(f), k)|.
* `IsDiscreteExchangeFamily` — A finite-set exchange property capturing one-step
  symmetric exchange, serving as a formal proxy for M-convexity.

## Main Results

* `coeff_pderivPow` — Coefficient formula for iterated single-variable partial
  derivative: involves ascending factorials.
* `coeff_iteratedPDeriv` — Full multi-index coefficient transport formula.
* `coeff_iteratedPDeriv_ne_zero_iff` — Support criterion: coeff β in the τ-th
  mixed derivative is nonzero iff coeff (β + τ) in f is nonzero.
* `mem_kthShadow_iff_exists_iteratedDerivative` — The exact k-th shadow theorem:
  β belongs to the k-th shadow of Supp(f) iff it appears in the support of some
  k-th order mixed partial derivative.
* `kthShadow_zero` — The 0-th shadow is the original set.
* `kthShadow_add` — Shadow composition law: Sh_b(Sh_a(S)) = Sh_{a+b}(S).

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open MvPolynomial Finsupp BigOperators Classical

noncomputable section

open IteratedShadowGeometry

/-! ## Core Definitions -/



/-
Alternative membership criterion using addition.
-/







/-! ## Basic Properties of pderivPow -/



/-! ## Coefficient Formula for Single-Variable Iterated Derivative -/

/-
The coefficient of `β` in `pderiv i` applied once to `f` equals
`(β i + 1) * coeff (β + eᵢ) f`.
-/

/-
The coefficient of `β` in `pderivPow i k f` equals
`ascFactorial (β i + 1) k * coeff (β + k • eᵢ) f`.
-/


/-
In characteristic zero with no zero divisors, `pderivPow i k f` has nonzero
coefficient at `β` iff `f` has nonzero coefficient at `β + k • eᵢ`.
-/

/-! ## Coefficient Formula for Full Iterated Mixed Derivative -/

/-
Auxiliary: `iteratedPDeriv` applied with the zero multi-index is the identity.
-/


/-
The Finsupp `τ` equals `∑ i : Fin n, τ i • Finsupp.single i 1`.
-/

/-
Helper: coefficient formula for foldr over a list of distinct variables.
-/

/-
The coefficient transport formula for the full iterated mixed derivative:
`coeff β (iteratedPDeriv τ f) = (∏ i, ascFactorial (β i + 1) (τ i)) * coeff (β + τ) f`.
-/

/-
The product of ascending factorials is always positive.
-/

/-
**Support criterion for iterated mixed derivatives** (characteristic zero):
`coeff β (iteratedPDeriv τ f) ≠ 0 ↔ coeff (β + τ) f ≠ 0`.
-/

/-! ## The 0-th Shadow -/

/-
The 0-th shadow of `S` is `S` itself.
-/

/-! ## Shadow Monotonicity -/

/-
The shadow operator is monotone in the support set.
-/

/-! ## The Semigroup Law: Shadow Composition -/

/-
**Shadow composition law (pointwise version):**
`β ∈ kthShadow (kthShadow S a) b ↔ β ∈ kthShadow S (a + b)`.

This says the shadow operator forms a genuine discrete flow: composing
an a-step shadow with a b-step shadow yields an (a+b)-step shadow.
The proof decomposes a total-mass-(a+b) multi-index into mass-a and mass-b parts.
-/

theorem IteratedShadowGeometry.mem_kthShadow_add_iff{n : ℕ} {S : Finset (Fin n →₀ ℕ)} {a b : ℕ}
    {β : Fin n →₀ ℕ} :
    β ∈ kthShadow (kthShadow S a) b ↔ β ∈ kthShadow S (a + b) := by sorry
