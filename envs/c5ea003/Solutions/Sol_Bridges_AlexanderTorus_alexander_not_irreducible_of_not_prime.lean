-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_not_irreducible_of_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T15:35:28.404593+00:00
-- url     : https://prove2.me/submissions/0b9d9893-be98-441a-a58c-2c8ef3a44e48

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

lemma divisors_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
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

theorem alexander_semiprime_factorization {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    alexander (p * q)
      = cyclotomic (2 * p) ℤ * cyclotomic (2 * q) ℤ * cyclotomic (2 * (p * q)) ℤ := by
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  have hN : Odd (p * q) := hpo.mul hqo
  have h1 : 1 < p * q := by nlinarith
  rw [alexander_eq_prod_cyclotomic hN h1, divisors_semiprime hp hq]
  have hpq : p ≠ p * q := by nlinarith
  have hqq : q ≠ p * q := by nlinarith
  have herase : ({1, p, q, p * q} : Finset ℕ).erase 1 = {p, q, p * q} := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, rfl | rfl | rfl | rfl⟩ <;> simp_all
    · rintro (rfl | rfl | rfl) <;> exact ⟨by omega, by simp⟩
  rw [herase, Finset.prod_insert (by simp [hne, hpq]), Finset.prod_insert (by simp [hqq]),
    Finset.prod_singleton, mul_assoc]

lemma totient_two_mul_of_odd {n : ℕ} (hn : Odd n) : Nat.totient (2 * n) = Nat.totient n := by
  rw [Nat.totient_mul (Nat.coprime_two_left.2 hn), Nat.totient_two, one_mul]

lemma natDegree_cyclotomic_two_mul_prime {p : ℕ} (hp : p.Prime) (hpo : Odd p) :
    (cyclotomic (2 * p) ℤ).natDegree = p - 1 := by
  rw [natDegree_cyclotomic, totient_two_mul_of_odd hpo, Nat.totient_prime hp]

lemma natDegree_cyclotomic_two_mul_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1) := by
  rw [natDegree_cyclotomic, totient_two_mul_of_odd (hpo.mul hqo),
    Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne), Nat.totient_prime hp,
    Nat.totient_prime hq]

theorem alexander_semiprime_factor_data {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    (cyclotomic (2 * p) ℤ).natDegree = p - 1 ∧
    (cyclotomic (2 * q) ℤ).natDegree = q - 1 ∧
    (cyclotomic (2 * (p * q)) ℤ).natDegree = (p - 1) * (q - 1) ∧
    Irreducible (cyclotomic (2 * p) ℤ) ∧ Irreducible (cyclotomic (2 * q) ℤ) ∧
    Irreducible (cyclotomic (2 * (p * q)) ℤ) := by
  have hpp := hp.pos
  have hqp := hq.pos
  refine ⟨natDegree_cyclotomic_two_mul_prime hp hpo,
    natDegree_cyclotomic_two_mul_prime hq hqo,
    natDegree_cyclotomic_two_mul_semiprime hp hq hpo hqo hne,
    cyclotomic.irreducible (by omega), cyclotomic.irreducible (by omega),
    cyclotomic.irreducible (by positivity)⟩

theorem alexander_semiprime_degree_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p - 1) + (q - 1) + (p - 1) * (q - 1) = p * q - 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp.one_lt.le
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq.one_lt.le
  have h : (1 + a) * (1 + b) = 1 + (a + b + a * b) := by ring
  simp only [Nat.add_sub_cancel_left, h]

/-! ## Recovering the factorization from the degree data -/

theorem totient_semiprime_and_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    Nat.totient (p * q) = (p - 1) * (q - 1) ∧
    p + q = p * q + 1 - Nat.totient (p * q) := by
  have ht : Nat.totient (p * q) = (p - 1) * (q - 1) := by
    rw [Nat.totient_mul ((Nat.coprime_primes hp hq).2 hne), Nat.totient_prime hp,
      Nat.totient_prime hq]
  refine ⟨ht, ?_⟩
  rw [ht]
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp.one_lt.le
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq.one_lt.le
  have h : (1 + a) * (1 + b) = 1 + (a + b + a * b) := by ring
  simp only [Nat.add_sub_cancel_left, h]
  omega

theorem recover_factors_from_degrees {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q)
    (s : ℕ) (hs : s = p * q + 1 - Nat.totient (p * q)) :
    (s - Nat.sqrt (s ^ 2 - 4 * (p * q))) / 2 = p ∧
    (s + Nat.sqrt (s ^ 2 - 4 * (p * q))) / 2 = q := by
  obtain ⟨-, hsum⟩ := totient_semiprime_and_sum hp hq hlt.ne
  have hspq : s = p + q := by omega
  have hdisc : s ^ 2 - 4 * (p * q) = (q - p) ^ 2 := by
    rw [hspq]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hlt.le
    have h : (p + (p + c)) ^ 2 = c ^ 2 + 4 * (p * (p + c)) := by ring
    simp only [Nat.add_sub_cancel_left]
    omega
  rw [hdisc, Nat.sqrt_eq']
  omega

lemma alexander_prime {N : ℕ} (hN : Odd N) (hprime : N.Prime) :
    alexander N = cyclotomic (2 * N) ℤ := by
  have h1 : 1 < N := hprime.one_lt
  rw [alexander_eq_prod_cyclotomic hN h1, hprime.divisors]
  have herase : ({1, N} : Finset ℕ).erase 1 = {N} := by
    ext d
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, rfl | rfl⟩ <;> simp_all
    · rintro rfl; exact ⟨by omega, by simp⟩
  rw [herase, Finset.prod_singleton]

theorem solution {N : ℕ} (hN : Odd N) (h1 : 1 < N)
    (hnp : ¬ N.Prime) : ¬ Irreducible (alexander N) := by
  obtain ⟨d, hdvd, hd1, hdN⟩ : ∃ d, d ∣ N ∧ d ≠ 1 ∧ d ≠ N := by
    obtain ⟨m, hm, hm1, hmN⟩ := Nat.exists_dvd_of_not_prime2 h1 hnp
    exact ⟨m, hm, by omega, by omega⟩
  have hpos : 0 < N := by omega
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hpos
  have hdmem : d ∈ N.divisors.erase 1 :=
    Finset.mem_erase.2 ⟨hd1, Nat.mem_divisors.2 ⟨hdvd, hpos.ne'⟩⟩
  have hfac : alexander N =
      cyclotomic (2 * d) ℤ * ∏ e ∈ (N.divisors.erase 1).erase d, cyclotomic (2 * e) ℤ := by
    rw [alexander_eq_prod_cyclotomic hN h1,
      ← Finset.mul_prod_erase _ (fun e => cyclotomic (2 * e) ℤ) hdmem]
  intro hirr
  have hdodd : Odd d := odd_of_dvd_odd hN hdvd
  have hdlt : d < N := lt_of_le_of_ne (Nat.le_of_dvd hpos hdvd) hdN
  set Q : ℤ[X] := ∏ e ∈ (N.divisors.erase 1).erase d, cyclotomic (2 * e) ℤ with hQ
  have hAne : alexander N ≠ 0 := alexander_ne_zero hN
  have hCne : cyclotomic (2 * d) ℤ ≠ 0 := fun h => hAne (by rw [hfac, h, zero_mul])
  have hQne : Q ≠ 0 := fun h => hAne (by rw [hfac, h, mul_zero])
  have hdegC : (cyclotomic (2 * d) ℤ).natDegree = Nat.totient d := by
    rw [natDegree_cyclotomic, totient_two_mul_of_odd hdodd]
  have hsum : (alexander N).natDegree = Nat.totient d + Q.natDegree := by
    rw [hfac, natDegree_mul hCne hQne, hdegC]
  have htot : Nat.totient d < d := Nat.totient_lt d (by omega)
  have hdegQ : 0 < Q.natDegree := by
    have hA := alexander_natDegree hN
    omega
  have hCpos : 0 < (cyclotomic (2 * d) ℤ).natDegree := by
    rw [hdegC]; exact Nat.totient_pos.2 hdpos
  rcases hirr.isUnit_or_isUnit hfac with hu | hu
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ hCpos) hu
  · exact (Polynomial.not_isUnit_of_natDegree_pos _ hdegQ) hu
