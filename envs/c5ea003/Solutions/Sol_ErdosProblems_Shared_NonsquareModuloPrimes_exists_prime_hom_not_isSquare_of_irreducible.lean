-- Prove2me | solution 1 for ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:42:46.548417+00:00
-- url     : https://prove2.me/submissions/6460485d-f0c6-4d18-bb6f-43edf31c2056

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_NonsquareModuloPrimes_exists_prime_hom_not_isSquare
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
    (b : 𝓞 K) (hb : ¬ IsSquare (algebraMap (𝓞 K) K b))
    [hirr : Fact (Irreducible (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X]))] (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  have hne : (X ^ 2 - C (algebraMap (𝓞 K) K b) : K[X]) ≠ 0 := hirr.out.ne_zero
  haveI hfinite := (AdjoinRoot.powerBasis hne).finite
  haveI : NumberField (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b))) :=
    NumberField.of_module_finite K _
  have hfin := (AdjoinRoot.powerBasis hne).finrank.trans
    ((AdjoinRoot.powerBasis_dim hne).trans (natDegree_X_pow_sub_C (n := 2)))
  have hγ : AdjoinRoot.root (X ^ 2 - C (algebraMap (𝓞 K) K b)) ^ 2 =
      algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b))) (algebraMap (𝓞 K) K b) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (algebraMap (𝓞 K) K b))
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
    rw [AdjoinRoot.algebraMap_eq]
    exact h
  have hγK : AdjoinRoot.root (X ^ 2 - C (algebraMap (𝓞 K) K b)) ∉
      Set.range (algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b)))) := by
    rintro ⟨y, hy⟩
    apply hb
    refine ⟨y, ?_⟩
    apply (algebraMap K (AdjoinRoot (X ^ 2 - C (algebraMap (𝓞 K) K b)))).injective
    rw [map_mul, hy, ← sq, hγ]
  exact exists_prime_hom_not_isSquare hfin b _ hγ hγK N
