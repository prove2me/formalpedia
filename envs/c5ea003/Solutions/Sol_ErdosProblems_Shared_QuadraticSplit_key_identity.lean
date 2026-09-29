-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.key_identity
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:19:48.44438+00:00
-- url     : https://prove2.me/submissions/88963561-9e23-4795-9ca6-a73544dbe917

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_trace_gen_eq_zero
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

omit [NumberField K] [NumberField M] in
theorem trace_algebraMap_mul (c : K) (y : M) :
    Algebra.trace K M (algebraMap K M c * y) = c * Algebra.trace K M y := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

theorem exists_eq_add_mul (hfin : Module.finrank K M = 2) (γ : M)
    (hγK : γ ∉ Set.range (algebraMap K M)) (x : M) :
    ∃ u v : K, x = algebraMap K M u + algebraMap K M v * γ := by
  have hli : LinearIndependent K ![(1 : M), γ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      refine ⟨?_, rfl⟩
      rwa [Algebra.smul_def, mul_one, map_eq_zero_iff _ (algebraMap K M).injective] at hst
    · exfalso
      apply hγK
      refine ⟨-(s / t), ?_⟩
      have htM : algebraMap K M t ≠ 0 := (map_ne_zero_iff _ (algebraMap K M).injective).mpr ht
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      apply mul_left_cancel₀ htM
      rw [← map_mul, show t * -(s / t) = -s by field_simp, map_neg]
      linear_combination -hst
  set bs := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hfin]) with hbs
  have h := bs.sum_repr x
  have h0 : bs 0 = 1 := by rw [hbs, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have h1 : bs 1 = γ := by rw [hbs, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  rw [Fin.sum_univ_two, h0, h1, Algebra.smul_def, Algebra.smul_def, mul_one] at h
  exact ⟨_, _, h.symm⟩

theorem trace_algebraMap_eq (hfin : Module.finrank K M = 2) (c : K) :
    Algebra.trace K M (algebraMap K M c) = 2 * c := by
  rw [Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat]
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (x : M) :
    algebraMap K M (2 * b) * x =
      algebraMap K M (b * Algebra.trace K M x) +
        algebraMap K M (Algebra.trace K M (γ * x)) * γ := by
  obtain ⟨u, v, rfl⟩ := exists_eq_add_mul hfin γ hγK x
  have hT0 := trace_gen_eq_zero b γ hγ hγK
  have e1 : Algebra.trace K M (algebraMap K M u + algebraMap K M v * γ) = 2 * u := by
    rw [map_add, trace_algebraMap_mul, trace_algebraMap_eq hfin, hT0, mul_zero, add_zero]
  have e2 : Algebra.trace K M (γ * (algebraMap K M u + algebraMap K M v * γ)) = 2 * (v * b) := by
    have hsplit : γ * (algebraMap K M u + algebraMap K M v * γ) =
        algebraMap K M u * γ + algebraMap K M (v * b) := by
      rw [map_mul, ← hγ]
      ring
    rw [hsplit, map_add, trace_algebraMap_mul, hT0, mul_zero, zero_add,
      trace_algebraMap_eq hfin]
  rw [e1, e2]
  simp only [map_mul, map_ofNat]
  ring
