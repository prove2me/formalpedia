-- Prove2me | Definitions.Def_Bridges_PosetTheory_IteratedShadowGeometry
-- name    : Bridges_PosetTheory_IteratedShadowGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:56.604512+00:00
-- url     : https://prove2.me/theorems/90db1efb-14f8-4730-861d-46573365203f
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_IteratedShadowGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.IteratedShadowGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/IteratedShadowGeometry.lean by skeleton subtraction
import Mathlib
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

namespace IteratedShadowGeometry

/-! ## Core Definitions -/

/-- The **k-th shadow** of a support set `S`: the set of all exponent vectors `β` such that
`β + τ ∈ S` for some multi-index `τ` with total mass `k`. Equivalently, all vectors
obtainable by subtracting a mass-k multi-index from an element of `S`. -/
def kthShadow {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (k : ℕ) : Finset (Fin n →₀ ℕ) :=
  S.biUnion (fun α =>
    ((Finset.Iic α).filter (fun τ => τ.sum (fun _ m => m) = k)).image (α - ·))


/-
Alternative membership criterion using addition.
-/

/-- The support of a multivariate polynomial as a `Finset`. -/
def finsuppSupport {n : ℕ} {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Fin n) R) : Finset (Fin n →₀ ℕ) :=
  f.support


/-- Apply `pderiv i` exactly `k` times. -/
def pderivPow {n : ℕ} {R : Type*} [CommSemiring R]
    (i : Fin n) (k : ℕ) (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  (⇑(MvPolynomial.pderiv i))^[k] f

/-- The **iterated mixed partial derivative** indexed by multi-index `τ`:
applies `pderiv i` exactly `τ i` times for each variable `i`. -/
def iteratedPDeriv {n : ℕ} {R : Type*} [CommSemiring R]
    (τ : Fin n →₀ ℕ) (f : MvPolynomial (Fin n) R) : MvPolynomial (Fin n) R :=
  (List.finRange n).foldr (fun i g => pderivPow i (τ i) g) f

/-- The **derivative shadow profile** of a polynomial: maps `k` to the cardinality
of the k-th shadow of its support. -/
def derivShadowProfile {n : ℕ} {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Fin n) R) : ℕ → ℕ :=
  fun k => (kthShadow (finsuppSupport f) k).card

/-- A finite set satisfies the **discrete exchange property** if for any two elements
`α, β ∈ S` and any coordinate `i` where `α i > β i`, there exists a coordinate `j`
where `β j > α j` such that `α - eᵢ + eⱼ ∈ S`.

This is a formal proxy for M-convexity of the support, capturing the symmetric
exchange axiom from discrete convex analysis and matroid theory. -/
def IsDiscreteExchangeFamily {n : ℕ} (S : Finset (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ i : Fin n, α i > β i →
    ∃ j : Fin n, β j > α j ∧
      α - Finsupp.single i 1 + Finsupp.single j 1 ∈ S

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


/-! ## The Exact k-th Shadow Theorem -/

/-
**The exact k-th shadow theorem:**
`β` belongs to the k-th shadow of `Supp(f)` if and only if there exists
a multi-index `τ` of total mass `k` such that `β` appears in the support
of the `τ`-th mixed partial derivative of `f`.

This is the main result: iterated differentiation has an exact combinatorial
footprint on exponent sets, governed precisely by the shadow operator.
-/


/-! ## Cross-Domain: Exchange Families and Shadow Geometry -/

/-
Any singleton set satisfies the exchange property vacuously.
-/



/-! ## Shadow of Empty and Universal Sets -/


/-
The 1-st shadow of a singleton.
-/

/-! ## Shadow of Unions -/

/-
The shadow distributes over unions of support sets.
-/



/-
The k-th shadow is empty when k exceeds the degree of every element in S.
-/


/-! ## Shadow Profile Monotonicity -/


end IteratedShadowGeometry


