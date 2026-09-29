-- Prove2me | solution 1 for MConvexCompression.exchangeVisible_eq_degreeShadow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:03:01.965722+00:00
-- url     : https://prove2.me/submissions/af976c7a-69bb-4161-b447-9302ff027eec

-- Sol generated from Bridges/GraphTheory/MConvexCompression.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_MConvexCompression
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

open MConvexCompression

/-! ## Part I: Core Definitions -/











/-! ## Part II: Shadow-Fiber Correspondence -/

/-- Shadow membership is equivalent to fiber nonemptiness. -/
theorem mem_shadow_iff_fiber_nonempty {n : ℕ}
    (S : Finset (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) :
    α ∈ SupportShadow S ↔ (DominatingFiber S α).Nonempty := by
  unfold SupportShadow DominatingFiber
  simp [Finset.Nonempty, Finset.mem_filter]


/-- The quadratic leaf fiber is a subset of the dominating fiber. -/
theorem quadLeafFiber_sub_dominatingFiber {n : ℕ}
    (S : Finset (Fin n →₀ ℕ)) (α : Fin n →₀ ℕ) :
    QuadraticLeafFiber S α ⊆ DominatingFiber S α := by
  intro β hβ
  simp only [QuadraticLeafFiber, DominatingFiber, Finset.mem_filter] at hβ ⊢
  exact ⟨hβ.1, hβ.2.1⟩

/-- The fiber of α relative to a homogeneous support equals
    the quadratic leaf fiber when `totalDeg α = r - 2`. -/
theorem fiber_eq_quadLeafFiber_of_homog {n : ℕ}
    (S : Finset (Fin n →₀ ℕ)) (r : ℕ) (hr : 2 ≤ r)
    (hS : IsHomogeneousSupport S r)
    (α : Fin n →₀ ℕ) (hα : totalDeg α = r - 2) :
    DominatingFiber S α = QuadraticLeafFiber S α := by
  ext β
  simp only [DominatingFiber, QuadraticLeafFiber, Finset.mem_filter]
  constructor
  · intro ⟨hβS, hαβ⟩
    exact ⟨hβS, hαβ, by rw [hS β hβS, hα]; omega⟩
  · intro ⟨hβS, hαβ, _⟩
    exact ⟨hβS, hαβ⟩

/-! ## Part III: No-Cancellation and Derivative Weights -/

/-- For polynomials with nonneg coefficients, no-cancellation holds everywhere. -/
theorem nonneg_coeff_no_cancellation {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (hp : ∀ d, MvPolynomial.coeff d p ≥ 0)
    (α : Fin n →₀ ℕ) : NoCancellationOnFiber p α :=
  fun β _ => hp β


/-
**Theorem 1 (Derivative Weight Positivity).**
    The derivative weight is positive when α ≤ β.
-/

/-
Each term in the derivative sum is nonneg when the coefficient is nonneg.
-/


/-! ## Part IV: Counting Compression -/





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


/-
Matroid basis supports are homogeneous.
-/


/-! ## Part IX: Shadow Coordinate Containment -/


/-
Shadow elements only use active coordinates.
-/


open MConvexCompression in
theorem solution{n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) (r : ℕ) (hr : 2 ≤ r)
    (hp_nonneg : ∀ d, MvPolynomial.coeff d p ≥ 0)
    (hS : IsHomogeneousSupport (NewtonSupportFinset p) r) :
    ExchangeVisibleShadow p (NewtonSupportFinset p) (r - 2) =
      DegreeShadow (NewtonSupportFinset p) (r - 2) := by
  ext α
  simp only [ExchangeVisibleShadow, DegreeShadow, Set.mem_setOf_eq]
  constructor
  · intro ⟨hdeg, hfib, _⟩
    refine ⟨?_, hdeg⟩
    rw [mem_shadow_iff_fiber_nonempty]
    exact Finset.Nonempty.mono (quadLeafFiber_sub_dominatingFiber _ α) hfib
  · intro ⟨hshad, hdeg⟩
    refine ⟨hdeg, ?_, nonneg_coeff_no_cancellation p hp_nonneg α⟩
    rw [mem_shadow_iff_fiber_nonempty] at hshad
    rw [← fiber_eq_quadLeafFiber_of_homog _ r hr hS α hdeg]
    exact hshad
