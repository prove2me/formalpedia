-- Prove2me | solution 1 for ErdosProblems.Shared.QuadraticSplit.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:28:37.999961+00:00
-- url     : https://prove2.me/submissions/71af2c86-d2c8-4cad-a70a-ff9582a16710

import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_trace_gen_eq_zero
import Theorems.Thm_ErdosProblems_Shared_QuadraticSplit_key_identity
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



theorem trace_algebraMap_eq (hfin : Module.finrank K M = 2) (c : K) :
    Algebra.trace K M (algebraMap K M c) = 2 * c := by
  rw [Algebra.trace_algebraMap, hfin, nsmul_eq_mul, Nat.cast_ofNat]





theorem trace_identity_one (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (x y : M) :
    2 * b * Algebra.trace K M (x * y) =
      b * Algebra.trace K M x * Algebra.trace K M y +
        Algebra.trace K M (γ * x) * Algebra.trace K M (γ * y) := by
  have h := key_identity hfin b γ hγ hγK x
  have h' : algebraMap K M (2 * b) * (x * y) =
      algebraMap K M (b * Algebra.trace K M x) * y +
        algebraMap K M (Algebra.trace K M (γ * x)) * (γ * y) := by
    rw [← mul_assoc, h]
    ring
  have h'' := congrArg (Algebra.trace K M) h'
  rw [trace_algebraMap_mul, map_add, trace_algebraMap_mul, trace_algebraMap_mul] at h''
  linear_combination h''

theorem trace_identity_two (hfin : Module.finrank K M = 2) (b : K) (γ : M)
    (hγ : γ ^ 2 = algebraMap K M b) (hγK : γ ∉ Set.range (algebraMap K M)) (hb : b ≠ 0)
    (x y : M) :
    2 * Algebra.trace K M (γ * (x * y)) =
      Algebra.trace K M x * Algebra.trace K M (γ * y) +
        Algebra.trace K M (γ * x) * Algebra.trace K M y := by
  have h := key_identity hfin b γ hγ hγK x
  have h' : algebraMap K M (2 * b) * (γ * (x * y)) =
      algebraMap K M (b * Algebra.trace K M x) * (γ * y) +
        algebraMap K M (Algebra.trace K M (γ * x) * b) * y := by
    rw [map_mul (algebraMap K M) (Algebra.trace K M (γ * x)) b, ← hγ]
    calc algebraMap K M (2 * b) * (γ * (x * y)) = γ * (algebraMap K M (2 * b) * x) * y := by
          ring
      _ = γ * (algebraMap K M (b * Algebra.trace K M x) +
            algebraMap K M (Algebra.trace K M (γ * x)) * γ) * y := by rw [h]
      _ = _ := by ring
  have h'' := congrArg (Algebra.trace K M) h'
  rw [trace_algebraMap_mul, map_add, trace_algebraMap_mul, trace_algebraMap_mul] at h''
  have hmul : b * (2 * Algebra.trace K M (γ * (x * y)) -
      (Algebra.trace K M x * Algebra.trace K M (γ * y) +
        Algebra.trace K M (γ * x) * Algebra.trace K M y)) = 0 := by
    linear_combination h''
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact absurd h0 hb
  · linear_combination h0

/-! ### The two extensions of `φ` to `𝓞 M` -/



theorem coe_trO (x : 𝓞 M) :
    algebraMap (𝓞 K) K (trO (K := K) x) = Algebra.trace K M (algebraMap (𝓞 M) M x) := rfl

omit [NumberField K] [NumberField M] in
theorem coe_algebraMap_ringOfIntegers (c : 𝓞 K) :
    algebraMap (𝓞 M) M (algebraMap (𝓞 K) (𝓞 M) c) = algebraMap K M (algebraMap (𝓞 K) K c) :=
  rfl
end ErdosProblems.Shared.QuadraticSplit

open NumberField Polynomial
variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.QuadraticSplit in
theorem solution (hfin : Module.finrank K M = 2) (b : 𝓞 K) (γ : 𝓞 M)
    (hγ : (γ : M) ^ 2 = algebraMap K M (b : K)) (hγK : (γ : M) ∉ Set.range (algebraMap K M))
    {ℓ : ℕ} (φ : 𝓞 K →+* ZMod ℓ) (t : ZMod ℓ) (ht : t ^ 2 = φ b)
    (w : ZMod ℓ) (hw1 : 2 * φ b * w = 1) :
    ∃ ψ : 𝓞 M →+* ZMod ℓ, (∀ c : 𝓞 K, ψ (algebraMap (𝓞 K) (𝓞 M) c) = φ c) ∧ ψ γ = t := by
  have hγ' : algebraMap (𝓞 M) M γ ^ 2 = algebraMap K M (algebraMap (𝓞 K) K b) := hγ
  have hγK' : algebraMap (𝓞 M) M γ ∉ Set.range (algebraMap K M) := hγK
  have hb : algebraMap (𝓞 K) K b ≠ 0 := by
    intro h
    apply hγK'
    refine ⟨0, ?_⟩
    rw [map_zero, eq_comm, ← pow_eq_zero_iff two_ne_zero, hγ', h, map_zero]
  have hT0 : Algebra.trace K M (algebraMap (𝓞 M) M γ) = 0 := trace_gen_eq_zero _ _ hγ' hγK'
  -- identities in `𝓞 K`
  have hU1 : trO (K := K) (1 : 𝓞 M) = 2 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_one, map_ofNat, ← map_one (algebraMap K M), trace_algebraMap_eq hfin,
      mul_one]
  have hV1 : trO (K := K) (γ * 1) = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, mul_one, hT0, map_zero]
  have hUalg : ∀ c : 𝓞 K, trO (K := K) (algebraMap (𝓞 K) (𝓞 M) c) = 2 * c := by
    intro c
    apply RingOfIntegers.coe_injective
    rw [coe_trO, coe_algebraMap_ringOfIntegers, trace_algebraMap_eq hfin, map_mul, map_ofNat]
  have hValg : ∀ c : 𝓞 K, trO (K := K) (γ * algebraMap (𝓞 K) (𝓞 M) c) = 0 := by
    intro c
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_mul, coe_algebraMap_ringOfIntegers, mul_comm, trace_algebraMap_mul, hT0,
      mul_zero, map_zero]
  have hUγ : trO (K := K) γ = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, hT0, map_zero]
  have hVγ : trO (K := K) (γ * γ) = 2 * b := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_mul, ← sq, hγ', trace_algebraMap_eq hfin, map_mul, map_ofNat]
  have hUadd : ∀ x y : 𝓞 M, trO (K := K) (x + y) = trO x + trO y := by
    intro x y
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_add, map_add, map_add, coe_trO, coe_trO]
  have hU0 : trO (K := K) (0 : 𝓞 M) = 0 := by
    apply RingOfIntegers.coe_injective
    rw [coe_trO, map_zero, map_zero, map_zero]
  have hI1 : ∀ x y : 𝓞 M, 2 * b * trO (K := K) (x * y) =
      b * trO x * trO y + trO (γ * x) * trO (γ * y) := by
    intro x y
    apply RingOfIntegers.coe_injective
    simp only [map_add, map_mul, map_ofNat, coe_trO]
    exact trace_identity_one hfin _ _ hγ' hγK' _ _
  have hI2 : ∀ x y : 𝓞 M, 2 * trO (K := K) (γ * (x * y)) =
      trO x * trO (γ * y) + trO (γ * x) * trO y := by
    intro x y
    apply RingOfIntegers.coe_injective
    simp only [map_add, map_mul, map_ofNat, coe_trO]
    exact trace_identity_two hfin _ _ hγ' hγK' hb _ _
  -- the extension
  let ψ : 𝓞 M →+* ZMod ℓ :=
    { toFun := fun x => (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w
      map_one' := by
        show (φ b * φ (trO (1 : 𝓞 M)) + φ (trO (γ * 1)) * t) * w = 1
        rw [hU1, hV1, map_ofNat, map_zero]
        linear_combination hw1
      map_mul' := by
        intro x y
        show (φ b * φ (trO (x * y)) + φ (trO (γ * (x * y))) * t) * w =
          (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w *
            ((φ b * φ (trO y) + φ (trO (γ * y)) * t) * w)
        have e1 := congrArg φ (hI1 x y)
        have e2 := congrArg φ (hI2 x y)
        simp only [map_add, map_mul, map_ofNat] at e1 e2
        linear_combination (-(φ b * φ (trO (x * y)) + φ (trO (γ * (x * y))) * t) * w) * hw1 +
          (w ^ 2 * φ b) * e1 + (w ^ 2 * φ b * t) * e2 -
          (w ^ 2 * φ (trO (γ * x)) * φ (trO (γ * y))) * ht
      map_zero' := by
        show (φ b * φ (trO (0 : 𝓞 M)) + φ (trO (γ * 0)) * t) * w = 0
        rw [mul_zero, hU0, map_zero]
        ring
      map_add' := by
        intro x y
        show (φ b * φ (trO (x + y)) + φ (trO (γ * (x + y))) * t) * w =
          (φ b * φ (trO x) + φ (trO (γ * x)) * t) * w +
            (φ b * φ (trO y) + φ (trO (γ * y)) * t) * w
        rw [mul_add, hUadd, hUadd, map_add, map_add]
        ring }
  refine ⟨ψ, fun c => ?_, ?_⟩
  · show (φ b * φ (trO (algebraMap (𝓞 K) (𝓞 M) c)) +
        φ (trO (γ * algebraMap (𝓞 K) (𝓞 M) c)) * t) * w = φ c
    rw [hUalg, hValg, map_mul, map_ofNat, map_zero]
    linear_combination φ c * hw1
  · show (φ b * φ (trO γ) + φ (trO (γ * γ)) * t) * w = t
    rw [hUγ, hVγ, map_mul, map_ofNat, map_zero]
    linear_combination t * hw1
