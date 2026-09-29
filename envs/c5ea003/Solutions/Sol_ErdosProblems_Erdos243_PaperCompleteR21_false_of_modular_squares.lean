-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR21.false_of_modular_squares
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:45:03.477461+00:00
-- url     : https://prove2.me/submissions/0c13b915-71ab-4229-a6bf-040d60d53f93

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Definitions.Def_ErdosProblems_Shared_QuadraticSplitPrimes
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR21_SquareSpecialisationDedekind
import Theorems.Thm_ErdosProblems_Shared_NonsquareModuloPrimes_exists_prime_hom_not_isSquare_of_not_isSquare
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.RingTheory.Trace.Basic

/-!
# Erdős 243: the square-specialisation lemma without the Chebotarev density theorem

Paper form of `long243:res:squarespec` of `paper/reasoning-parts/erdos243/core.tex`
(lemma at line 303): `f ∈ ℚ[T]` irreducible with root `α`, `H (α) ≠ 0`, and for all but finitely
many primes `ℓ` every root `r` of `f` modulo `ℓ` has `H (r)` a nonzero square modulo `ℓ`
(stated through integral models `G = d f`, `J = d ^ 2 H`); then `H (α)` is a square in `ℚ(α)`.

The paper derives this from the Chebotarev density theorem.  Here it follows from
`ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare`, whose only analytic
input is the simple pole of the Dedekind zeta function at `s = 1`, already in Mathlib.

The reduction.  Put `K = ℚ[T] / (f)` with `α` the class of `T`, and `c` the leading coefficient
of `G`.  Then `a = c α` is integral, and for a polynomial `P ∈ ℤ[T]` and `e ≥ deg P` the element
`∑_{j ≤ e} P_j c ^ (e - j) a ^ j` of `𝓞 K` equals `c ^ e P (α)`; under any ring homomorphism
`φ : 𝓞 K → ZMod ℓ` it becomes `c ^ e P (r)` with `r = φ (a) / c`.  Taking `P = G` shows that
`r` is a root of `G` modulo `ℓ`, and taking `P = J`, `e = 2 deg J`, gives an element
`b = (c ^ (deg J) d) ^ 2 H (α)` of `𝓞 K` with `φ (b) = (c ^ (deg J)) ^ 2 J (r)`.  If `H (α)` were
not a square in `K`, neither would `b` be, and some prime `ℓ` beyond every bound would make
`φ (b)` zero or a non-square, contradicting the hypothesis at the root `r`.

`squareSpecialisation_holds` is the statement of
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisation` written out in full, so this file
depends on Mathlib and the `Shared` number-field files only.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR21
open NumberField Polynomial



theorem map_scaledEval {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : Polynomial ℤ) (c : ℤ) (e : ℕ) (a : R) :
    φ (scaledEval P c e a) = scaledEval P c e (φ a) := by
  simp only [scaledEval, map_sum, map_mul, map_pow, map_intCast]

theorem scaledEval_mul {R : Type*} [CommRing R] (P : Polynomial ℤ) (c : ℤ) (e : ℕ)
    (hP : P.natDegree ≤ e) (r : R) :
    scaledEval P c e ((c : R) * r) = (c : R) ^ e * (P.map (Int.castRingHom R)).eval r := by
  rw [scaledEval, Polynomial.eval_eq_sum_range' (n := e + 1)
    (lt_of_le_of_lt (natDegree_map_le) (Nat.lt_succ_of_le hP)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hje : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpow : (c : R) ^ e = (c : R) ^ (e - j) * (c : R) ^ j := (pow_sub_mul_pow _ hje).symm
  rw [coeff_map, eq_intCast, hpow]
  push_cast
  ring

theorem eval_map_int_eq_eval₂ {K : Type*} [Field K] [CharZero K] (α : K) (P : Polynomial ℤ) :
    (P.map (Int.castRingHom K)).eval α =
      (P.map (Int.castRingHom ℚ)).eval₂ (Rat.castHom K) α := by
  rw [eval_map, eval₂_map]
  congr 1
  exact RingHom.ext_int _ _
end ErdosProblems.Erdos243.PaperCompleteR21

open NumberField Polynomial
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR21 in
theorem solution {K : Type*} [Field K] [NumberField K] (α : K)
    (f H : Polynomial ℚ) (hf0 : f ≠ 0) (hfα : f.eval₂ (Rat.castHom K) α = 0)
    (hnsq : ¬ IsSquare (H.eval₂ (Rat.castHom K) α))
    (d : ℕ) (hd : 0 < d) (G J : Polynomial ℤ)
    (hG : G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f)
    (hJ : J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H)
    (hmod : ∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) :
    False := by
  classical
  obtain ⟨Nmod, hNmod⟩ := hmod
  -- the leading coefficient of `G` and the integral element `a = c α`
  have hG0 : G ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hG
    have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
    exact hf0 ((mul_eq_zero.mp hG.symm).resolve_left (by simpa using hd0))
  set c : ℤ := G.leadingCoeff with hc
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hG0
  have hGeval : (G.map (Int.castRingHom K)).eval α = 0 := by
    rw [eval_map_int_eq_eval₂, hG, eval₂_mul, eval₂_C, hfα, mul_zero]
  have hGα : Polynomial.aeval α G = 0 := by
    rw [aeval_def, algebraMap_int_eq, ← eval_map]
    exact hGeval
  have ha : IsIntegral ℤ (c • α) := isIntegral_leadingCoeff_smul G α hGα
  let a : 𝓞 K := ⟨c • α, ha⟩
  have hacoe : algebraMap (𝓞 K) K a = (c : K) * α := by
    show c • α = (c : K) * α
    rw [zsmul_eq_mul]
  -- the element `b` of `𝓞 K`
  set k := J.natDegree with hk
  obtain ⟨b, hbdef⟩ : ∃ b : 𝓞 K, b = scaledEval J c (2 * k) a := ⟨_, rfl⟩
  have hJeval : (J.map (Int.castRingHom K)).eval α =
      ((d : K) ^ 2) * H.eval₂ (Rat.castHom K) α := by
    rw [eval_map_int_eq_eval₂, hJ, eval₂_mul, eval₂_C]
    simp
  have hbcoe : algebraMap (𝓞 K) K b = ((c : K) ^ k * d) ^ 2 * H.eval₂ (Rat.castHom K) α := by
    rw [hbdef, map_scaledEval, hacoe, scaledEval_mul J c (2 * k) (by omega), hJeval]
    ring
  -- `b` is not a square in `K`
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.mpr hc0
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hbnsq : ¬ IsSquare (algebraMap (𝓞 K) K b) := by
    rintro ⟨y, hy⟩
    apply hnsq
    refine ⟨y / ((c : K) ^ k * d), ?_⟩
    have hne : (c : K) ^ k * d ≠ 0 := mul_ne_zero (pow_ne_zero _ hcK) hdK
    rw [hbcoe] at hy
    field_simp
    linear_combination hy
  -- a prime `ℓ` beyond every bound at which `b` is not a nonzero square
  obtain ⟨ℓ, hℓ, hℓN, φ, hφ⟩ :=
    ErdosProblems.Shared.NonsquareModuloPrimes.exists_prime_hom_not_isSquare_of_not_isSquare b
      hbnsq (max Nmod c.natAbs)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  -- `c` is a unit modulo `ℓ`
  have hcℓ : (c : ZMod ℓ) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    have hle : ℓ ≤ c.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) (Int.natCast_dvd.mp h)
    exact absurd (lt_of_le_of_lt (le_max_right _ _) hℓN) (not_lt.mpr hle)
  -- the root `r` of `G` modulo `ℓ`
  set r : ZMod ℓ := φ a * (c : ZMod ℓ)⁻¹ with hr
  have hφa : φ a = (c : ZMod ℓ) * r := by
    rw [hr, mul_left_comm, mul_inv_cancel₀ hcℓ, mul_one]
  have hGr : (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 := by
    have hzero : scaledEval G c G.natDegree a = 0 := by
      apply RingOfIntegers.coe_injective
      rw [map_scaledEval, hacoe, scaledEval_mul G c G.natDegree le_rfl, hGeval, mul_zero,
        map_zero]
    have h := congrArg φ hzero
    rw [map_scaledEval, hφa, scaledEval_mul G c G.natDegree le_rfl, map_zero] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hcℓ)
  obtain ⟨hJne, s, hs⟩ := hNmod ℓ hℓ (lt_of_le_of_lt (le_max_left _ _) hℓN) r hGr
  have hφb : φ b = (c : ZMod ℓ) ^ (2 * k) * (J.map (Int.castRingHom (ZMod ℓ))).eval r := by
    rw [hbdef, map_scaledEval, hφa, scaledEval_mul J c (2 * k) (by omega)]
  apply hφ
  refine ⟨?_, ⟨(c : ZMod ℓ) ^ k * s, ?_⟩⟩
  · rw [hφb]
    exact mul_ne_zero (pow_ne_zero _ hcℓ) hJne
  · rw [hφb, hs]
    ring
