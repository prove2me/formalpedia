-- Prove2me | solution 1 for IteratedShadowGeometry.mem_kthShadow_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:18.350609+00:00
-- url     : https://prove2.me/submissions/6311478e-3ee7-4683-9174-dc36eac75184

-- Sol generated from Bridges/PosetTheory/IteratedShadowGeometry.lean
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


/-- Membership criterion for `kthShadow`. -/
theorem mem_kthShadow_iff {n : ℕ} {S : Finset (Fin n →₀ ℕ)} {k : ℕ} {β : Fin n →₀ ℕ} :
    β ∈ kthShadow S k ↔
      ∃ α ∈ S, ∃ τ : Fin n →₀ ℕ, τ ≤ α ∧ τ.sum (fun _ m => m) = k ∧ β = α - τ := by
  simp only [kthShadow, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter,
    Finset.mem_Iic]
  constructor
  · rintro ⟨α, hα, τ, ⟨hτle, hτsum⟩, rfl⟩
    exact ⟨α, hα, τ, hτle, hτsum, rfl⟩
  · rintro ⟨α, hα, τ, hτle, hτsum, rfl⟩
    exact ⟨α, hα, τ, ⟨hτle, hτsum⟩, rfl⟩

/-
Alternative membership criterion using addition.
-/
theorem mem_kthShadow_iff' {n : ℕ} {S : Finset (Fin n →₀ ℕ)} {k : ℕ} {β : Fin n →₀ ℕ} :
    β ∈ kthShadow S k ↔
      ∃ τ : Fin n →₀ ℕ, τ.sum (fun _ m => m) = k ∧ β + τ ∈ S := by
  refine' ⟨ fun h => _, fun h => _ ⟩;
  · obtain ⟨ α, hα, τ, hτ, hβ ⟩ := mem_kthShadow_iff.mp h;
    exact ⟨ τ, hβ.1, by simpa [ hβ.2, tsub_add_cancel_of_le hτ ] using hα ⟩;
  · obtain ⟨ τ, hτ₁, hτ₂ ⟩ := h; use mem_kthShadow_iff.2 ⟨ β + τ, hτ₂, τ, by aesop ⟩ ;







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



open IteratedShadowGeometry in
theorem solution{n : ℕ} {S : Finset (Fin n →₀ ℕ)} {a b : ℕ}
    {β : Fin n →₀ ℕ} :
    β ∈ kthShadow (kthShadow S a) b ↔ β ∈ kthShadow S (a + b) := by
  rw [ mem_kthShadow_iff', mem_kthShadow_iff' ];
  constructor <;> intro h;
  · obtain ⟨ τ, hτ₁, hτ₂ ⟩ := h; rw [ mem_kthShadow_iff' ] at hτ₂; obtain ⟨ τ', hτ'₁, hτ'₂ ⟩ := hτ₂; use τ + τ'; simp_all +decide [ add_assoc, Finsupp.sum_add_index' ] ;
    ring;
  · obtain ⟨ τ, hτ₁, hτ₂ ⟩ := h;
    -- We need to find a τ₁ ≤ τ with sum τ₁ = a. This can be done by choosing any τ₁ ≤ τ with sum τ₁ = a (and then τ₂ = τ - τ₁ has sum b).
    obtain ⟨τ₁, hτ₁_le, hτ₁_sum⟩ : ∃ τ₁ : Fin n →₀ ℕ, τ₁ ≤ τ ∧ τ₁.sum (fun _ m => m) = a := by
      -- We can construct such a τ₁ by iteratively subtracting 1 from the largest component of τ until the sum is reduced to a.
      have h_subtract : ∀ {τ : Fin n →₀ ℕ} {a : ℕ}, a ≤ τ.sum (fun _ m => m) → ∃ τ₁ : Fin n →₀ ℕ, τ₁ ≤ τ ∧ τ₁.sum (fun _ m => m) = a := by
        intros τ a ha;
        exact?;
      exact h_subtract ( by linarith );
    refine' ⟨ τ - τ₁, _, _ ⟩;
    · have h_sum_split : (τ.sum (fun _ m => m)) = (τ₁.sum (fun _ m => m)) + ((τ - τ₁).sum (fun _ m => m)) := by
        rw [ ← Finsupp.sum_add_index' ] <;> aesop;
      linarith;
    · refine' mem_kthShadow_iff'.mpr ⟨ τ₁, hτ₁_sum, _ ⟩;
      convert hτ₂ using 1;
      rw [ add_assoc, tsub_add_cancel_of_le hτ₁_le ]
