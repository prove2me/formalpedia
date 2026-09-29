-- Prove2me | solution 3 for flt5_zz5_kummer_pid_root
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:34:36.736821+00:00
-- url     : https://prove2.me/submissions/e991642a-c3f0-436b-9c5d-e998a37dcb62

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib
set_option maxRecDepth 100000
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option linter.all false

open NumberField Ideal

namespace AgentGFLT5

abbrev K := CyclotomicField 5 ℚ

instance hcyc : IsCyclotomicExtension {5} ℚ K := CyclotomicField.isCyclotomicExtension 5 ℚ
instance : NumberField K := IsCyclotomicExtension.numberField {5} ℚ K
instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

noncomputable def F (p : ℕ) : ℕ := if p = 5 then 1 else orderOf (p : ZMod 5)

lemma F_dvd_four (p : ℕ) (hp : p.Prime) : F p ∣ 4 := by
  unfold F
  split_ifs with h
  · exact one_dvd _
  · apply orderOf_dvd_of_pow_eq_one
    have h0 : (p : ZMod 5) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h5
      exact h ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5).symm
    have := ZMod.pow_card_sub_one_eq_one h0
    simpa using this

lemma normP (p : ℕ) (hp : p.Prime) (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})] : absNorm P = p ^ F p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [absNorm_eq_pow_inertiaDeg' P hp]
  congr 1
  unfold F
  split_ifs with h
  · subst h
    exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime 5 K P
  · exact IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 5) p K P
      (fun hd => h ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hd))


lemma exists_prime_under (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (span {(p : ℤ)}) := by
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal <| under ℤ P
  have hp0 : p ≠ 0 := fun h ↦ hP0 <|
    eq_bot_of_comap_eq_bot (R := ℤ) <| by simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hpr : Prime p := hpprime (hP.under _)
  have hlies : P.LiesOver (span {p}) := by
    rcases abs_choice p with h | h <;>
    simpa [h, span_singleton_neg p, ← submodule_span_eq, ← hp] using over_under P
  have hspan : span {((p.natAbs : ℕ) : ℤ)} = span {p} := by
    rcases abs_choice p with h | h <;> simp [h]
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hpr, ?_⟩
  rw [hspan]; exact hlies

lemma F_dvd_fact (I : Ideal (𝓞 K)) (p : ℕ) (hp : p.Prime) :
    I ≠ ⊥ → F p ∣ (absNorm I).factorization p := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _
    rw [Ideal.isUnit_iff.mp hx, absNorm_top]
    simp
  | h₃ a P ha hPp ih =>
    intro _
    haveI hPI : P.IsPrime := Ideal.isPrime_of_prime hPp
    have hP0 : P ≠ ⊥ := hPp.ne_zero
    have hn1 : absNorm P ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
    have hn2 : absNorm a ≠ 0 := by rwa [Ne, absNorm_eq_zero_iff]
    rw [map_mul, Nat.factorization_mul hn1 hn2, Finsupp.add_apply]
    refine dvd_add ?_ (ih ha)
    obtain ⟨q, hq, hlies⟩ := exists_prime_under P hP0
    rw [normP q hq P, hq.factorization_pow, Finsupp.single_apply]
    split_ifs with hqp
    · subst hqp; exact dvd_refl _
    · exact dvd_zero _


lemma exists_primeP (p : ℕ) (hp : p.Prime) :
    ∃ P : Ideal (𝓞 K), absNorm P = p ^ F p := by
  haveI : (span {(p : ℤ)}).IsPrime :=
    (span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  obtain ⟨P, _, hP1, hP2⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) (by
      rw [← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).mp (algebraMap ℤ (𝓞 K)).injective_int]
      exact bot_le)
  haveI := hP1
  haveI : P.LiesOver (span {(p : ℤ)}) := (liesOver_iff _ _).mpr hP2.symm
  exact ⟨P, normP p hp P⟩

lemma exists_ideal (n : ℕ) :
    n ≠ 0 → (∀ p, p.Prime → F p ∣ n.factorization p) → ∃ J : Ideal (𝓞 K), absNorm J = n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro _ h
    have hk' := h p hp
    rw [hp.factorization_pow, Finsupp.single_eq_same] at hk'
    obtain ⟨P, hP⟩ := exists_primeP p hp
    refine ⟨P ^ (k / F p), ?_⟩
    rw [map_pow, hP, ← pow_mul, Nat.mul_div_cancel' hk']
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact ⟨⊤, absNorm_top⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have hfa : ∀ p, p.Prime → F p ∣ a.factorization p := by
      intro p hp
      have := h p hp
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply] at this
      by_cases hpa : p ∣ a
      · have hpb : ¬ p ∣ b := (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpa hab)
        rwa [Nat.factorization_eq_zero_of_not_dvd hpb, add_zero] at this
      · rw [Nat.factorization_eq_zero_of_not_dvd hpa]; exact dvd_zero _
    have hfb : ∀ p, p.Prime → F p ∣ b.factorization p := by
      intro p hp
      have := h p hp
      rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply] at this
      by_cases hpb : p ∣ b
      · have hpa : ¬ p ∣ a := (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpb hab.symm)
        rwa [Nat.factorization_eq_zero_of_not_dvd hpa, zero_add] at this
      · rw [Nat.factorization_eq_zero_of_not_dvd hpb]; exact dvd_zero _
    obtain ⟨Ja, hJa⟩ := iha ha0 hfa
    obtain ⟨Jb, hJb⟩ := ihb hb0 hfb
    exact ⟨Ja * Jb, by rw [map_mul, hJa, hJb]⟩


lemma norm_nonneg_K (x : K) : 0 ≤ Algebra.norm ℚ x := by
  classical
  haveI : IsTotallyComplex K := IsCyclotomicExtension.Rat.isTotallyComplex (n := 5) K (by norm_num)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv RingHom.equivRatAlgHom (fun f => f x) (fun φ => φ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ => φ x)] at h
  have hfib : ∀ w : InfinitePlace K,
      ∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x =
        ((Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
    intro w
    have hw : InfinitePlace.IsComplex w := IsTotallyComplex.isComplex w
    have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
      intro h'
      have : ComplexEmbedding.IsReal w.embedding := by
        rw [ComplexEmbedding.isReal_iff]; exact h'.symm
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr hw) (InfinitePlace.isReal_iff.mpr this)
    have hset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)) =
        {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
      ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      conv_lhs => rw [← InfinitePlace.mk_embedding w]
      rw [eq_comm, InfinitePlace.mk_eq_iff]
      constructor
      · rintro (h' | h')
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
      · rintro (h' | h')
        · exact Or.inl h'.symm
        · exact Or.inr h'.symm
    rw [hset, Finset.prod_pair hne, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]
  simp_rw [hfib] at h
  rw [← Complex.ofReal_prod] at h
  have h2 : ((Algebra.norm ℚ x : ℝ) : ℂ) = ((∏ w : InfinitePlace K,
      Complex.normSq (w.embedding x) : ℝ) : ℂ) := by
    rw [← h]; simp
  have h3 := Complex.ofReal_injective h2
  have h4 : (0 : ℝ) ≤ (Algebra.norm ℚ x : ℝ) := by
    rw [h3]; exact Finset.prod_nonneg (fun w _ => Complex.normSq_nonneg _)
  exact_mod_cast h4


lemma norm_nonneg_O (x : 𝓞 K) : 0 ≤ Algebra.norm ℤ x := by
  have h := Algebra.coe_norm_int x
  have := norm_nonneg_K (x : K)
  rw [← h] at this
  exact_mod_cast this

lemma norm_zero_O : Algebra.norm ℤ (0 : 𝓞 K) = 0 := by
  have h := Algebra.coe_norm_int (0 : 𝓞 K)
  have h2 : ((0 : 𝓞 K) : K) = 0 := rfl
  have h3 : Algebra.norm ℚ (0 : K) = 0 := Algebra.norm_zero
  rw [h2, h3] at h
  exact_mod_cast h

/-- core: if `N(α) = c * s^5` with `c ∈ {1, 5}` then `s` is a norm. -/
theorem core (α : 𝓞 K) (s : ℤ) (c : ℕ) (hc : c = 1 ∨ c = 5)
    (h : Algebra.norm ℤ α = (c : ℤ) * s ^ 5) : ∃ d : 𝓞 K, Algebra.norm ℤ d = s := by
  have hc0 : (c : ℤ) ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
  by_cases hs : s = 0
  · refine ⟨0, ?_⟩
    rw [hs, norm_zero_O]
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [norm_zero_O] at h
    exact hs (pow_eq_zero_iff (n := 5) (by norm_num) |>.mp
      ((mul_eq_zero.mp h.symm).resolve_left hc0))
  have hspan0 : span {α} ≠ ⊥ := by
    rwa [Ne, span_singleton_eq_bot]
  have habs : absNorm (span {α}) = c * s.natAbs ^ 5 := by
    rw [absNorm_span_singleton, h, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hs0 : s.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hs
  have hcond : ∀ p, p.Prime → F p ∣ s.natAbs.factorization p := by
    intro p hp
    have h1 := F_dvd_fact (span {α}) p hp hspan0
    have hcn : c ≠ 0 := by rcases hc with rfl | rfl <;> norm_num
    rw [habs, Nat.factorization_mul hcn (pow_ne_zero _ hs0), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at h1
    by_cases hp5 : p = 5
    · subst hp5; simp [F]
    · have hcp : c.factorization p = 0 := by
        rcases hc with rfl | rfl
        · simp
        · rw [Nat.Prime.factorization (by norm_num : Nat.Prime 5), Finsupp.single_apply,
            if_neg (Ne.symm hp5)]
      rw [hcp, zero_add] at h1
      have hcop : Nat.Coprime (F p) 5 :=
        Nat.Coprime.coprime_dvd_left (F_dvd_four p hp) (by norm_num)
      exact hcop.dvd_of_dvd_mul_left h1
  obtain ⟨J, hJ⟩ := exists_ideal s.natAbs hs0 hcond
  haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.five_pid K
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal J).principal
  rw [hd, submodule_span_eq, absNorm_span_singleton] at hJ
  have hd_nn := norm_nonneg_O d
  have hs_nn : 0 ≤ s := by
    have hα := norm_nonneg_O α
    rw [h] at hα
    have hcpos : (0 : ℤ) < c := by rcases hc with rfl | rfl <;> norm_num
    have : 0 ≤ s ^ 5 := nonneg_of_mul_nonneg_right (by linarith) hcpos
    exact (Odd.pow_nonneg_iff (by decide)).mp this
  exact ⟨d, (Int.natAbs_inj_of_nonneg_of_nonneg hd_nn hs_nn).mp hJ⟩


lemma finrank_K : Module.finrank ℚ K = 4 := by
  rw [IsCyclotomicExtension.finrank K
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
  decide

lemma norm_z_add (c : ℚ) :
    Algebra.norm ℚ (IsCyclotomicExtension.zeta 5 ℚ K + algebraMap ℚ K c) =
      c ^ 4 - c ^ 3 + c ^ 2 - c + 1 := by
  classical
  set z := IsCyclotomicExtension.zeta 5 ℚ K
  have hz : IsPrimitiveRoot z 5 := IsCyclotomicExtension.zeta_spec 5 ℚ K
  let pb := hz.powerBasis ℚ
  have hgen : pb.gen = z := hz.powerBasis_gen ℚ
  have hdim : pb.dim = 4 := by rw [← pb.finrank, finrank_K]
  let M := Algebra.leftMulMatrix pb.basis z
  have hchar : M.charpoly = Polynomial.cyclotomic 5 ℚ := by
    change (Algebra.leftMulMatrix pb.basis z).charpoly = _
    rw [← hgen, charpoly_leftMulMatrix, hgen,
      hz.minpoly_eq_cyclotomic_of_irreducible
        (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
  have heval := Matrix.eval_charpoly M (-c)
  rw [hchar, Polynomial.cyclotomic_prime] at heval
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, zero_add,
    Polynomial.eval_finset_sum] at heval
  have hmat : Matrix.scalar (Fin pb.dim) (-c) - M =
      -(Algebra.leftMulMatrix pb.basis (z + algebraMap ℚ K c)) := by
    rw [map_add, AlgHom.commutes]
    change Matrix.scalar (Fin pb.dim) (-c) - M = -(M + algebraMap ℚ _ c)
    rw [Matrix.algebraMap_eq_diagonal]
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h, sub_eq_add_neg, Pi.algebraMap_apply]
  rw [hmat, Matrix.det_neg, Fintype.card_fin] at heval
  have hsign : (-1 : ℚ) ^ pb.dim = 1 := by rw [hdim]; norm_num
  rw [hsign, one_mul] at heval
  rw [Algebra.norm_eq_matrix_det pb.basis, ← heval]
  ring


lemma norm_phi (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec 5 ℚ K).toInteger * (b : 𝓞 K)) =
      a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 := by
  set z := IsCyclotomicExtension.zeta 5 ℚ K
  have hcoe : (((a : 𝓞 K) + (IsCyclotomicExtension.zeta_spec 5 ℚ K).toInteger * (b : 𝓞 K) :
      𝓞 K) : K) = algebraMap ℚ K a + z * algebraMap ℚ K b := by
    simp [z]
  have h := Algebra.coe_norm_int ((a : 𝓞 K) +
      (IsCyclotomicExtension.zeta_spec 5 ℚ K).toInteger * (b : 𝓞 K))
  rw [hcoe] at h
  suffices hq : Algebra.norm ℚ (algebraMap ℚ K a + z * algebraMap ℚ K b) =
      ((a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 : ℤ) : ℚ) by
    rw [hq] at h; exact_mod_cast h
  by_cases hb : b = 0
  · subst hb
    simp only [Int.cast_zero, map_zero, mul_zero, add_zero]
    rw [Algebra.norm_algebraMap, finrank_K]
    push_cast; ring
  · have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
    have heq : algebraMap ℚ K a + z * algebraMap ℚ K b =
        algebraMap ℚ K b * (z + algebraMap ℚ K ((a : ℚ) / b)) := by
      rw [mul_add, ← map_mul, mul_div_cancel₀ _ hbq]
      ring
    rw [heq, map_mul, Algebra.norm_algebraMap, finrank_K, norm_z_add]
    field_simp
    push_cast
    ring

theorem kummer_main (s : ℤ) (β : 𝓞 K) (hβ : Algebra.norm ℤ β = s ^ 5) :
    ∃ d : 𝓞 K, (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  obtain ⟨d, hd⟩ := core β s 1 (Or.inl rfl) (by rw [hβ]; simp)
  exact ⟨d, by rw [hd]⟩

theorem phi_main (a b s : ℤ)
    (hPhi : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 = 5 * s ^ 5) :
    ∃ d : 𝓞 K, (Algebra.norm ℤ d) ^ 5 = s ^ 5 := by
  obtain ⟨d, hd⟩ := core _ s 5 (Or.inr rfl) (by rw [norm_phi, hPhi]; norm_num)
  exact ⟨d, by rw [hd]⟩

end AgentGFLT5

theorem _root_.solution (a b s : ℤ) (h_cop : Int.gcd a b = 1) (β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) (hβ : Algebra.norm ℤ β = s ^ 5) (hPID : IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))) : ∃ d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ), (Algebra.norm ℤ d) ^ 5 = s ^ 5 :=
  AgentGFLT5.kummer_main s β hβ

#print axioms solution
