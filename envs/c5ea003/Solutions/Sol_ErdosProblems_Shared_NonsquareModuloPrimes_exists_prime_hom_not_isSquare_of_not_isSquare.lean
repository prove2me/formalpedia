-- Prove2me | solution 1 for ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:43:45.695528+00:00
-- url     : https://prove2.me/submissions/8b108977-ab88-4d3d-8794-842124fccb44

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_NonsquareModuloPrimes_exists_prime_hom_not_isSquare_of_irreducible
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Trace.Basic

namespace ErdosProblems.Shared.NonsquareModuloPrimes
end ErdosProblems.Shared.NonsquareModuloPrimes

/-!
# A non-square of a number field stays a non-square modulo infinitely many primes

**Theorem** (`exists_prime_hom_not_isSquare`).  Let `K ⊆ M` be number fields with
`[M : K] = 2`, `M = K(γ)` and `γ ^ 2 = b ∈ 𝓞 K`.  Then for every `N` there are a prime `ℓ > N`
and a ring homomorphism `φ : 𝓞 K → ZMod ℓ` such that `φ b` is zero or a non-square.

This is the qualitative instance of the Chebotarev density theorem needed for the
square-specialisation lemma of Erdős #243, proved here from the simple pole of the Dedekind
zeta function (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`) alone, by the classical
comparison of Dirichlet series at `s = 1`.  Suppose instead that `φ b` is a nonzero square for every
`φ` into every `ZMod ℓ` with `ℓ > N`.  Call a prime `𝔭` of `𝓞 K` good if its norm is a prime
`ℓ > max N 2`.  Then

* every good `𝔭` is the kernel of some `φ : 𝓞 K → ZMod ℓ`, `φ b = t ^ 2` with `t ≠ 0`, and the
  two extensions of `φ` to `𝓞 M` (`γ ↦ ± t`) have distinct kernels of norm `ℓ` above `𝔭`
  (`QuadraticSplit.exists_split_primes_of_forall_isSquare`);
* so the ideals of `𝓞 K` supported on good primes, counted in pairs, inject into the ideals
  of `𝓞 M` with the same norm (`IdealCounting.sum_countSupp_mul_le`), while every ideal of
  `𝓞 K` factors into a good and a bad part (`IdealCounting.card_le_sum_countSupp`), and the
  bad part has a convergent Dirichlet series at `s = 1` (`IdealCounting.sum_countSupp_div_le`);
* hence `ζ_K(s) ^ 2 ≤ B ^ 2 ζ_M(s)` for real `s > 1` near `1`, which is incompatible with both
  zeta functions having a simple pole at `s = 1` (`DirichletPole.false_of_pole_comparison`).
-/

noncomputable section

namespace ErdosProblems.Shared.NonsquareModuloPrimes
open NumberField Ideal Filter Topology
end ErdosProblems.Shared.NonsquareModuloPrimes

open NumberField Ideal Filter Topology
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.NonsquareModuloPrimes in
open Polynomial in

theorem solution {K : Type*} [Field K] [NumberField K]
    (b : 𝓞 K) (hb : ¬ IsSquare (algebraMap (𝓞 K) K b)) (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  haveI : Fact (Irreducible (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X])) := ⟨by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_sub_C]
      simp
    · intro y hy
      apply hb
      refine ⟨y, ?_⟩
      rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hy
      rw [← hy, sq]⟩
  exact exists_prime_hom_not_isSquare_of_irreducible b hb N
