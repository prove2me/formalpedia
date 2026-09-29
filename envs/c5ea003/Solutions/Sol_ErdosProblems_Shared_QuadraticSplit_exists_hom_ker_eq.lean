-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.exists_hom_ker_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:13:22.085538+00:00
-- url     : https://prove2.me/submissions/73de36df-7f51-48f3-9eae-de0dd3d2a221

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















/-! ### The two extensions of `φ` to `𝓞 M` -/









/-! ### Kernels -/
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution {ℓ : ℕ} (hℓ : ℓ.Prime) (𝔭 : Ideal (𝓞 K))
    (h : Ideal.absNorm 𝔭 = ℓ) : ∃ φ : 𝓞 K →+* ZMod ℓ, RingHom.ker φ = 𝔭 := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hfin : Finite (𝓞 K ⧸ 𝔭) :=
    (Ideal.absNorm_ne_zero_iff 𝔭).mp (by rw [h]; exact hℓ.ne_zero)
  letI : Fintype (𝓞 K ⧸ 𝔭) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ 𝔭) = ℓ := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h]
  haveI : CharP (𝓞 K ⧸ 𝔭) ℓ := charP_of_card_eq_prime hcard
  let e := ZMod.ringEquiv (𝓞 K ⧸ 𝔭) hcard
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔭), ?_⟩
  ext x
  rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
