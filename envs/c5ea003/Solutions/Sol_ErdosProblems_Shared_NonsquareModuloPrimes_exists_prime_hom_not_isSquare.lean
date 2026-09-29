-- Prove2me | solution 1 for ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:41:05.641911+00:00
-- url     : https://prove2.me/submissions/8e1e9f0f-0984-4ea7-a04e-1c04476e354f

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_DirichletPole_false_of_pole_comparison
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_card_le_sum_countSupp
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_countSupp_le
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_sum_countSupp_div_le
import Theorems.Thm_ErdosProblems_Shared_IdealCounting_sum_countSupp_mul_le
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_exists_split_primes_of_forall_isSquare
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
theorem solution {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M (b : K)) (hγK : γ ∉ Set.range (algebraMap K M)) (N : ℕ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ N < ℓ ∧ ∃ φ : 𝓞 K →+* ZMod ℓ, ¬ (φ b ≠ 0 ∧ IsSquare (φ b)) := by
  classical
  by_contra hcon'
  have hcon : ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b) := by
    intro ℓ hℓ hlt φ
    by_contra h
    exact hcon' ⟨ℓ, hℓ, hlt, φ, h⟩
  have hγint : IsIntegral ℤ γ := by
    have hb : IsIntegral ℤ (algebraMap K M (b : K)) :=
      (RingOfIntegers.isIntegral_coe b).map (algebraMap K M).toIntAlgHom
    have h2 : IsIntegral ℤ (γ ^ 2) := by rw [hγ]; exact hb
    exact IsIntegral.of_pow two_pos h2
  let γ' : 𝓞 M := ⟨γ, hγint⟩
  set N₀ := max N 2 with hN₀
  have H : ∀ ℓ : ℕ, ℓ.Prime → N₀ < ℓ → ∀ φ : 𝓞 K →+* ZMod ℓ, φ b ≠ 0 ∧ IsSquare (φ b) :=
    fun ℓ hℓ hlt φ => hcon ℓ hℓ (lt_of_le_of_lt (le_max_left _ _) hlt) φ
  have hsplit := QuadraticSplit.exists_split_primes_of_forall_isSquare hfin b γ' hγ hγK N₀
    (le_max_right _ _) H
  obtain ⟨B, hB⟩ := IdealCounting.sum_countSupp_div_le (K := K) N₀
  have hga : ∀ n, (IdealCounting.countSupp K
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ) ≤
        (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) := fun n => by
    exact_mod_cast IdealCounting.countSupp_le (K := K)
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n
  have h1 : ∀ n, n ≠ 0 → (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) ≤
      DirichletPole.dconv
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ)) n := by
    intro n hn
    simp only [DirichletPole.dconv]
    exact_mod_cast IdealCounting.card_le_sum_countSupp (K := K)
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) hn
  have h2 : ∀ n, n ≠ 0 →
      DirichletPole.dconv
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
        (fun n => (IdealCounting.countSupp K
          (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ)) n ≤
        (Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ) := by
    intro n hn
    simp only [DirichletPole.dconv]
    exact_mod_cast IdealCounting.sum_countSupp_mul_le (K := K) M
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) hsplit hn
  have hA : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => ((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ)) s)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_natCast]
    exact tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hM : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => ((Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ) : ℂ)) s)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue M : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_natCast]
    exact tendsto_sub_one_mul_dedekindZeta_nhdsGT M
  exact DirichletPole.false_of_pole_comparison
    (a := fun n => (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ))
    (g := fun n => (IdealCounting.countSupp K
      (fun 𝔭 => Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭) n : ℝ))
    (b := fun n => (IdealCounting.countSupp K
      (fun 𝔭 => ¬ (Nat.Prime (absNorm 𝔭) ∧ N₀ < absNorm 𝔭)) n : ℝ))
    (m := fun n => (Nat.card {Q : Ideal (𝓞 M) // absNorm Q = n} : ℝ))
    (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _) (fun n => Nat.cast_nonneg _)
    hga h1 h2 B hB (dedekindZeta_residue_pos K) (dedekindZeta_residue_ne_zero M) hA hM
