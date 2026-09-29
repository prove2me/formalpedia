-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.trace_gen_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:13:23.233759+00:00
-- url     : https://prove2.me/submissions/cb6002cb-e540-4438-95ed-2aff468bfa0e

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
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
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution (b : K) (γ : M) (hγ : γ ^ 2 = algebraMap K M b)
    (hγK : γ ∉ Set.range (algebraMap K M)) : Algebra.trace K M γ = 0 := by
  have hirr : Irreducible (X ^ 2 - C b : K[X]) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_sub_C]
      simp
    · intro c hc
      apply hγK
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hc
      have hc' : algebraMap K M c ^ 2 = algebraMap K M b := by rw [← map_pow, hc]
      have h2 : (γ - algebraMap K M c) * (γ + algebraMap K M c) = 0 := by
        linear_combination hγ - hc'
      rcases mul_eq_zero.mp h2 with h | h
      · exact ⟨c, (sub_eq_zero.mp h).symm⟩
      · exact ⟨-c, by rw [map_neg]; linear_combination -h⟩
  have hmin : minpoly K γ = X ^ 2 - C b :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hγ])
      (monic_X_pow_sub_C b two_ne_zero)).symm
  have hnext : (X ^ 2 - C b : K[X]).nextCoeff = 0 := by
    rw [nextCoeff, natDegree_X_pow_sub_C]
    simp
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnext, neg_zero, mul_zero]
