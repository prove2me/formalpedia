-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.exists_split_primes_of_forall_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:37:58.00932+00:00
-- url     : https://prove2.me/submissions/5717f94a-dc4c-4a43-b76f-0bb87a54812c

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_exists_hom_ker_eq
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_exists_split_primes
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Trace.Basic

/-!
# Degree-one primes that split in a quadratic extension

Let `K ⊆ M` be number fields with `[M : K] = 2` and `M = K(γ)`, `γ ^ 2 = b ∈ 𝓞 K`.  A ring
homomorphism `φ : 𝓞 K → ZMod ℓ` (`ℓ` an odd prime) with `φ b = t ^ 2`, `t ≠ 0`, extends to two
distinct ring homomorphisms `𝓞 M → ZMod ℓ`, sending `γ` to `t` and to `-t`.

The ring of integers of `M` is not described explicitly.  Instead every `x ∈ M` satisfies

`2 b x = b · Tr(x) + Tr(γ x) · γ`        (`Tr = Tr_{M/K}`),

because `x = u + v γ` with `Tr x = 2 u` and `Tr (γ x) = 2 b v`.  For `x ∈ 𝓞 M` both traces lie in
`𝓞 K`, so `x ↦ (φ b · φ (Tr x) + φ (Tr (γ x)) · t) / (2 φ b)` is defined on `𝓞 M`; it is
multiplicative because of the two trace identities `trace_identity_one` and
`trace_identity_two`, which follow from the displayed formula.

The kernels of the two extensions are two distinct primes of `𝓞 M` of norm `ℓ`, both lying over
the kernel of `φ`.  `exists_split_primes_of_forall_isSquare` packages this in the form consumed by
`ErdosProblems.Shared.IdealCounting.sum_countSupp_mul_le`.
-/

noncomputable section

namespace ErdosProblems.Shared.QuadraticSplit
open NumberField Polynomial

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

/-! ### The quadratic extension `M = K(γ)` -/















/-! ### The two extensions of `φ` to `𝓞 M` -/









/-! ### Kernels -/
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution (hfin : Module.finrank K M = 2) (b : 𝓞 K)
    (γ : 𝓞 M) (hγ : (γ : M) ^ 2 = algebraMap K M (b : K))
    (hγK : (γ : M) ∉ Set.range (algebraMap K M)) (N₀ : ℕ) (hN₀ : 2 ≤ N₀)
    (H : ∀ ℓ : ℕ, ℓ.Prime → N₀ < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b)) :
    ∀ 𝔭 : Ideal (𝓞 K), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (Nat.Prime (Ideal.absNorm 𝔭) ∧ N₀ < Ideal.absNorm 𝔭) →
      ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
        Ideal.absNorm Q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm Q₂ = Ideal.absNorm 𝔭 ∧
        Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
        Q₁ ≠ Q₂ := by
  intro 𝔭 _ _ hP
  obtain ⟨hpr, hbig⟩ := hP
  obtain ⟨φ, hker⟩ := exists_hom_ker_eq hpr 𝔭 rfl
  obtain ⟨hne, r, hr⟩ := H _ hpr hbig φ
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hne (by rw [hr, mul_zero])
  exact exists_split_primes hfin b γ hγ hγK hpr (by omega) 𝔭 φ hker rfl r
    (by rw [hr, sq]) hr0
