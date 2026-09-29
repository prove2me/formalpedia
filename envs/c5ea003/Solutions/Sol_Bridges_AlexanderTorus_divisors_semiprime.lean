-- Prove2me | solution 1 for Bridges.AlexanderTorus.divisors_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T15:10:19.718007+00:00
-- url     : https://prove2.me/submissions/af9f8476-685c-4d8c-a4c0-33ef554b0ea0

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset

@[simp] lemma alexander_zero : alexander 0 = 0 := by simp [alexander]

lemma alexander_succ (N : ℕ) :
    alexander (N + 1) = alexander N + (-1) ^ N * X ^ N := by
  simp [alexander, Finset.sum_range_succ]

lemma X_add_one_mul_alexander (N : ℕ) :
    (X + 1) * alexander N = 1 - (-1) ^ N * X ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [alexander_succ, mul_add, ih, pow_succ (-1 : ℤ[X]) n, pow_succ X n]
      ring

lemma X_add_one_mul_alexander_odd {N : ℕ} (hN : Odd N) :
    (X + 1) * alexander N = X ^ N + 1 := by
  rw [X_add_one_mul_alexander, hN.neg_one_pow]
  ring

lemma alexander_ne_zero {N : ℕ} (hN : Odd N) : alexander N ≠ 0 := by
  intro h
  have hkey := X_add_one_mul_alexander_odd hN
  rw [h, mul_zero] at hkey
  have h0 := congrArg (Polynomial.eval 1) hkey
  simp at h0

lemma odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := (he.two_dvd).trans hd
    rw [Nat.odd_iff] at hN
    omega
  · exact ho

lemma divisors_two_mul {N : ℕ} (hpos : 0 < N) :
    (2 * N).divisors = N.divisors ∪ (N.divisors.image (fun d => 2 * d)) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hdvd, -⟩
    rcases Nat.even_or_odd d with he | ho
    · obtain ⟨e, rfl⟩ := he
      refine Or.inr ⟨e, ⟨?_, hpos.ne'⟩, by ring⟩
      have h : (2 : ℕ) * e ∣ 2 * N := by simpa [two_mul] using hdvd
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).1 h
    · exact Or.inl ⟨Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.2 ho) hdvd,
        hpos.ne'⟩
  · rintro (⟨hdvd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨hdvd.mul_left 2, by positivity⟩
    · exact ⟨mul_dvd_mul_left 2 he, by positivity⟩

lemma disjoint_divisors_image_two_mul {N : ℕ} (hN : Odd N) :
    Disjoint N.divisors (N.divisors.image (fun d => 2 * d)) := by
  rw [Finset.disjoint_right]
  rintro a ha ha'
  simp only [Finset.mem_image, Nat.mem_divisors] at ha ha'
  obtain ⟨e, -, rfl⟩ := ha
  obtain ⟨hdvd, -⟩ := ha'
  obtain ⟨k, hk⟩ := (dvd_mul_right 2 e).trans hdvd
  rw [Nat.odd_iff] at hN
  omega

/-! ## The cyclotomic factorization -/

theorem prod_cyclotomic_two_mul_divisors {N : ℕ} (hN : Odd N) (hpos : 0 < N) :
    ∏ d ∈ N.divisors, cyclotomic (2 * d) ℤ = X ^ N + 1 := by
  have key : (∏ d ∈ N.divisors, cyclotomic d ℤ) * (∏ d ∈ N.divisors, cyclotomic (2 * d) ℤ)
      = X ^ (2 * N) - 1 := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega) ℤ, divisors_two_mul hpos,
      Finset.prod_union (disjoint_divisors_image_two_mul hN),
      Finset.prod_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by norm_num) h)]
  rw [prod_cyclotomic_eq_X_pow_sub_one hpos ℤ] at key
  have hne : (X ^ N - 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp [zero_pow hpos.ne'] at h0
  refine mul_left_cancel₀ hne ?_
  rw [key, two_mul, pow_add]
  ring

theorem alexander_eq_prod_cyclotomic {N : ℕ} (hN : Odd N) (h1 : 1 < N) :
    alexander N = ∏ d ∈ N.divisors.erase 1, cyclotomic (2 * d) ℤ := by
  have hpos : 0 < N := by omega
  have hmem : (1 : ℕ) ∈ N.divisors := Nat.one_mem_divisors.2 hpos.ne'
  have hsplit := Finset.mul_prod_erase _ (fun d => cyclotomic (2 * d) ℤ) hmem
  rw [prod_cyclotomic_two_mul_divisors hN hpos] at hsplit
  simp only [mul_one, cyclotomic_two] at hsplit
  have hne : (X + 1 : ℤ[X]) ≠ 0 := by
    intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  refine mul_left_cancel₀ hne ?_
  rw [X_add_one_mul_alexander_odd hN, ← hsplit]

theorem alexander_natDegree {N : ℕ} (hN : Odd N) : (alexander N).natDegree = N - 1 := by
  have hpos : 0 < N := hN.pos
  have h := X_add_one_mul_alexander_odd hN
  have hX1 : (X + 1 : ℤ[X]) ≠ 0 := fun hc => by
    simpa using congrArg (Polynomial.eval 0) hc
  have hdeg : ((X + 1 : ℤ[X]) * alexander N).natDegree
      = (X + 1 : ℤ[X]).natDegree + (alexander N).natDegree :=
    natDegree_mul hX1 (alexander_ne_zero hN)
  have hXd : (X + 1 : ℤ[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C (1 : ℤ)
  have hR : ((X : ℤ[X]) ^ N + 1).natDegree = N := by
    have hC : ((X : ℤ[X]) ^ N + 1) = (X ^ N + C 1) := by simp
    rw [hC, natDegree_X_pow_add_C]
  rw [h, hR, hXd] at hdeg
  omega

/-! ## Knot determinant -/

theorem knot_determinant (N : ℕ) : (alexander N).eval (-1) = (N : ℤ) := by
  simp [alexander, eval_finset_sum, ← mul_pow]

theorem alexander_eval_one {N : ℕ} (hN : Odd N) : (alexander N).eval 1 = 1 := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (X_add_one_mul_alexander_odd hN)
  simp at h
  omega

theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p * q).divisors = {1, p, q, p * q} := by
  have hpq : p * q ≠ 0 := Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hdvd, -⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.1 hdvd
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp a ha) with rfl | rfl <;>
      rcases (Nat.Prime.eq_one_or_self_of_dvd hq b hb) with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨one_dvd _, hpq⟩
    · exact ⟨dvd_mul_right _ _, hpq⟩
    · exact ⟨dvd_mul_left _ _, hpq⟩
    · exact ⟨dvd_rfl, hpq⟩
