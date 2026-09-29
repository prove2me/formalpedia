-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.exists_split_primes
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:32:16.004021+00:00
-- url     : https://prove2.me/submissions/20e9f67e-6584-4695-b6ff-129d339c3598

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_exists_extension
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

theorem absNorm_ker {L : Type*} [Field L] [NumberField L] {ℓ : ℕ}
    (ψ : 𝓞 L →+* ZMod ℓ) : Ideal.absNorm (RingHom.ker ψ) = ℓ := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective ψ)).toEquiv,
    Nat.card_zmod]



theorem two_ne_zero_zmod {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  intro h
  have h' : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : 𝓞 M)
    (hγ : (γ : M) ^ 2 = algebraMap K M (b : K)) (hγK : (γ : M) ∉ Set.range (algebraMap K M))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (𝔭 : Ideal (𝓞 K)) (φ : 𝓞 K →+* ZMod ℓ)
    (hker : RingHom.ker φ = 𝔭) (hnorm : Ideal.absNorm 𝔭 = ℓ)
    (t : ZMod ℓ) (ht : t ^ 2 = φ b) (ht0 : t ≠ 0) :
    ∃ Q₁ Q₂ : Ideal (𝓞 M), Q₁.IsPrime ∧ Q₁ ≠ ⊥ ∧ Q₂.IsPrime ∧ Q₂ ≠ ⊥ ∧
      Ideal.absNorm Q₁ = Ideal.absNorm 𝔭 ∧ Ideal.absNorm Q₂ = Ideal.absNorm 𝔭 ∧
      Q₁.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧ Q₂.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 ∧
      Q₁ ≠ Q₂ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h2 := two_ne_zero_zmod hℓ hℓ2
  have hb0 : φ b ≠ 0 := by
    rw [← ht]
    exact pow_ne_zero 2 ht0
  have h2b : (2 : ZMod ℓ) * φ b ≠ 0 := mul_ne_zero h2 hb0
  obtain ⟨w, hw1⟩ : ∃ w : ZMod ℓ, 2 * φ b * w = 1 := ⟨(2 * φ b)⁻¹, mul_inv_cancel₀ h2b⟩
  obtain ⟨ψ₁, hψ₁, hψ₁γ⟩ := exists_extension hfin b γ hγ hγK φ t ht w hw1
  obtain ⟨ψ₂, hψ₂, hψ₂γ⟩ :=
    exists_extension hfin b γ hγ hγK φ (-t) (by rw [neg_sq, ht]) w hw1
  have hnormQ : ∀ ψ : 𝓞 M →+* ZMod ℓ, Ideal.absNorm (RingHom.ker ψ) = Ideal.absNorm 𝔭 :=
    fun ψ => by rw [absNorm_ker, hnorm]
  have hbot : ∀ ψ : 𝓞 M →+* ZMod ℓ, RingHom.ker ψ ≠ ⊥ := by
    intro ψ h
    have := absNorm_ker ψ
    rw [h, Ideal.absNorm_bot] at this
    exact hℓ.ne_zero this.symm
  have hcomap : ∀ ψ : 𝓞 M →+* ZMod ℓ, (∀ c : 𝓞 K, ψ (algebraMap (𝓞 K) (𝓞 M) c) = φ c) →
      (RingHom.ker ψ).comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭 := by
    intro ψ hψ
    rw [RingHom.comap_ker, ← hker]
    congr 1
    exact RingHom.ext hψ
  refine ⟨RingHom.ker ψ₁, RingHom.ker ψ₂, RingHom.ker_isPrime ψ₁, hbot ψ₁,
    RingHom.ker_isPrime ψ₂, hbot ψ₂, hnormQ ψ₁, hnormQ ψ₂, hcomap ψ₁ hψ₁, hcomap ψ₂ hψ₂, ?_⟩
  obtain ⟨c, hc⟩ := ZMod.ringHom_surjective φ t
  intro heq
  have hz : γ - algebraMap (𝓞 K) (𝓞 M) c ∈ RingHom.ker ψ₁ := by
    rw [RingHom.mem_ker, map_sub, hψ₁γ, hψ₁, hc, sub_self]
  rw [heq, RingHom.mem_ker, map_sub, hψ₂γ, hψ₂, hc] at hz
  apply ht0
  have h2t : (2 : ZMod ℓ) * t = 0 := by linear_combination -hz
  rcases mul_eq_zero.mp h2t with h | h
  · exact absurd h h2
  · exact h
