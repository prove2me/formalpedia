-- Prove2me | Definitions.Def_Bridges_GraphTheory_MConvexCompression
-- name    : Bridges_GraphTheory_MConvexCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:22.184473+00:00
-- url     : https://prove2.me/theorems/25729f2a-5997-43c6-b4c6-9aa82aaa3494
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_MConvexCompression
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.MConvexCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/MConvexCompression.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Universal M-Convex Compression Theorem

This file establishes that the complexity of Lorentzian recognition for
homogeneous polynomials with nonnegative coefficients is controlled by
the discrete-convex geometry (M-convex shadow) of the Newton support.

## Main Results

* `mem_shadow_iff_fiber_nonempty` — shadow membership ↔ fiber nonemptiness
* `nonneg_coeff_no_cancellation` — nonneg coefficients ⟹ no cancellation
* `fiber_eq_quadLeafFiber_of_homog` — fiber = quad leaf fiber for homogeneous supports
* `derivWeight_pos` — derivative weights are positive
* `mconvex_fiber_exchange` — M-convex exchange controls fibers
* `exchangeVisible_eq_degreeShadow` — visible shadow = full shadow for nonneg coeff
* `matroidBasisSupport_homogeneous` — matroid basis supports are homogeneous

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open Finset BigOperators MvPolynomial Finsupp

noncomputable section

namespace MConvexCompression

/-! ## Part I: Core Definitions -/

/-- The Newton support of a polynomial as a Finset. -/
def NewtonSupportFinset {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Finset (Fin n →₀ ℕ) :=
  p.support

/-- The total degree of a multi-index. -/
def totalDeg {n : ℕ} (α : Fin n →₀ ℕ) : ℕ :=
  α.sum fun _ m => m

/-- The support shadow: all multi-indices dominated by some support element. -/
def SupportShadow {n : ℕ} (S : Finset (Fin n →₀ ℕ)) : Set (Fin n →₀ ℕ) :=
  {α | ∃ β ∈ S, α ≤ β}

/-- The degree-k shadow: elements of the support shadow with total degree k. -/
def DegreeShadow {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    Set (Fin n →₀ ℕ) :=
  {α | α ∈ SupportShadow S ∧ totalDeg α = k}

/-- The dominating fiber: support elements that dominate a given multi-index. -/
def DominatingFiber {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) :
    Finset (Fin n →₀ ℕ) :=
  S.filter fun β => α ≤ β

/-- The quadratic leaf fiber: support elements that dominate α with
    total degree exactly `totalDeg α + 2`. -/
def QuadraticLeafFiber {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) :
    Finset (Fin n →₀ ℕ) :=
  S.filter fun β => α ≤ β ∧ totalDeg β = totalDeg α + 2

/-- No-cancellation condition: all coefficients above α are nonneg. -/
def NoCancellationOnFiber {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (α : Fin n →₀ ℕ) : Prop :=
  ∀ β, α ≤ β → MvPolynomial.coeff β p ≥ 0

/-- The exchange-visible shadow: degree-k shadow elements where the
    quadratic leaf fiber is nonempty and no-cancellation holds. -/
def ExchangeVisibleShadow {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (S : Finset (Fin n →₀ ℕ)) (k : ℕ) : Set (Fin n →₀ ℕ) :=
  {α | totalDeg α = k ∧
       (QuadraticLeafFiber S α).Nonempty ∧
       NoCancellationOnFiber p α}

/-- M-convex exchange property for sets of `Fin n →₀ ℕ`. -/
def IsMConvexExchange {n : ℕ} (S : Set (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ S, ∀ β ∈ S, ∀ i : Fin n,
    α i > β i →
    ∃ j : Fin n, α j < β j ∧
      (α - Finsupp.single i 1 + Finsupp.single j 1) ∈ S

/-- Homogeneity: all support elements have the same total degree. -/
def IsHomogeneousSupport {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (r : ℕ) : Prop :=
  ∀ β ∈ S, totalDeg β = r

/-! ## Part II: Shadow-Fiber Correspondence -/





/-! ## Part III: No-Cancellation and Derivative Weights -/


/-- The multinomial derivative weight: the product of descending factorials
    that appears when differentiating x^β by ∂^α. -/
def derivWeight {n : ℕ} (α β : Fin n →₀ ℕ) : ℕ :=
  Finset.univ.prod fun i => Nat.descFactorial (β i) (α i)

/-
**Theorem 1 (Derivative Weight Positivity).**
    The derivative weight is positive when α ≤ β.
-/

/-
Each term in the derivative sum is nonneg when the coefficient is nonneg.
-/


/-! ## Part IV: Counting Compression -/

/-- The shadow Finset: all multi-indices of degree k dominated by some element of S. -/
def MConvexShadowFinset {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (k : ℕ) :
    Finset (Fin n →₀ ℕ) :=
  (S.biUnion fun β => Finset.Iic β).filter fun α => totalDeg α = k


/-- The count of nonzero quadratic leaves. -/
def quadraticLeafCount {n : ℕ} (S : Finset (Fin n →₀ ℕ)) (r : ℕ) : ℕ :=
  (MConvexShadowFinset S (r - 2)).card


/-! ## Part V: M-Convex Exchange Structure on Fibers -/

/-
**Theorem 4 (M-Convex Fiber Exchange).**
    If S is M-convex and β₁, β₂ are in the dominating fiber above α,
    then M-convex exchange applies directly to β₁ and β₂.
-/

/-! ## Part VI: Exchange-Visible Shadow Equals Full Shadow -/


/-! ## Part VII: Cross-Domain — Flow Polytope Supports -/




/-
**Exchange Direction Existence.**
    When two Finsupps have the same total degree and differ at coordinate i,
    there must exist a compensating coordinate j in the other direction.
    This is a fundamental lemma used in all M-convex exchange arguments.
-/

/-! ## Part VIII: Matroid Specialization -/

/-- A matroid basis family gives a multiaffine support. -/
def matroidBasisSupport {n : ℕ} (bases : Finset (Finset (Fin n))) :
    Finset (Fin n →₀ ℕ) :=
  bases.image fun B => B.sum fun i => Finsupp.single i 1

/-
Matroid basis supports are homogeneous.
-/


/-! ## Part IX: Shadow Coordinate Containment -/

/-- Active coordinates appearing in at least one support element. -/
def activeCoords {n : ℕ} (S : Finset (Fin n →₀ ℕ)) : Finset (Fin n) :=
  S.biUnion fun β => Finset.univ.filter fun i => β i ≠ 0

/-
Shadow elements only use active coordinates.
-/

end MConvexCompression


