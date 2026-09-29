-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:59:25.668357+00:00
-- url     : https://prove2.me/submissions/c66247fa-922d-4543-ba6b-0a4c464b386d

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Bridges/AlexanderKnotNumberBridge.lean ====
/-
# A Knot–Number Theory Bridge: the Alexander polynomial of the torus knot `T(2,N)`

The Alexander polynomial of the `(2,N)` torus knot is (up to normalization)

  `A_N(X) = (X^N + 1) / (X + 1) = ∑_{i < N} (-1)^i X^i`   (`N` odd).

This file proves that `A_N` is, over `ℤ`, the product of the cyclotomic polynomials
`Φ_{2d}` for the divisors `d > 1` of `N`; in particular the *multiset of degrees of
its irreducible factors* is `{φ(d) : d ∣ N, d > 1}`, which for a semiprime `N = pq`
is `{p-1, q-1, (p-1)(q-1)}`, from which `φ(N)`, `p+q` and finally `p, q` are recovered.

Main results:

* `Bridges.AlexanderTorus.prod_cyclotomic_two_mul_divisors` :
  `∏_{d ∣ N} Φ_{2d} = X^N + 1` for odd `N > 0`.
* `Bridges.AlexanderTorus.alexander_eq_prod_cyclotomic` :
  `A_N = ∏_{d ∣ N, d ≠ 1} Φ_{2d}`.
* `Bridges.AlexanderTorus.alexander_semiprime_factorization` :
  `A_{pq} = Φ_{2p} · Φ_{2q} · Φ_{2pq}` for distinct odd primes `p ≠ q`, together with
  `alexander_semiprime_factor_data`: irreducibility of the three factors and their
  degrees `p-1`, `q-1`, `(p-1)(q-1)`.
* `Bridges.AlexanderTorus.alexander_irreducible_iff_prime` :
  for odd `N > 1`, `A_N` is irreducible over `ℤ` **iff** `N` is prime.
* `Bridges.AlexanderTorus.recover_factors_from_degrees` :
  the two primes are recovered from the degree data by
  `p = (s - √(s² - 4N))/2`, `q = (s + √(s² - 4N))/2` with `s = N + 1 - φ(N)`.
* `Bridges.AlexanderTorus.knot_determinant` : `A_N(-1) = N`
  (the determinant of the torus knot `T(2,N)`), and
  `alexander_natDegree` : `deg A_N = N - 1` (the "catch": exponential size in `log N`).
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The Alexander polynomial of `T(2,N)` -/

-- [dropped: platform already declares alexander]
@[simp] lemma alexander_zero : alexander 0 = 0 := by simp [alexander]

lemma alexander_succ (N : ℕ) :
    alexander (N + 1) = alexander N + (-1) ^ N * X ^ N := by
  simp [alexander, Finset.sum_range_succ]

/-- The defining relation: `(X+1) · A_N = 1 - (-1)^N X^N`. -/
lemma X_add_one_mul_alexander (N : ℕ) :
    (X + 1) * alexander N = 1 - (-1) ^ N * X ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [alexander_succ, mul_add, ih, pow_succ (-1 : ℤ[X]) n, pow_succ X n]
      ring

/-- For odd `N`, `(X+1) · A_N = X^N + 1`. -/
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

/-! ## Elementary divisor combinatorics -/

lemma odd_of_dvd_odd {N d : ℕ} (hN : Odd N) (hd : d ∣ N) : Odd d := by
  rcases Nat.even_or_odd d with he | ho
  · exfalso
    obtain ⟨k, hk⟩ := (he.two_dvd).trans hd
    rw [Nat.odd_iff] at hN
    omega
  · exact ho

/-- The divisors of `2N` are the divisors of `N` together with their doubles. -/
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

/-- For odd `N`, the divisors of `N` and their doubles are disjoint families. -/
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

/-- **Key identity.** For odd `N > 0`, `X^N + 1 = ∏_{d ∣ N} Φ_{2d}(X)` in `ℤ[X]`. -/
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

/-- **The bridge.** For odd `N > 1` the Alexander polynomial of `T(2,N)` is the product of
the cyclotomic polynomials `Φ_{2d}` over the divisors `d > 1` of `N`. -/
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

/-! ## Degree of `A_N` (the "catch": exponential in `log N`) -/

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

/-- The determinant of the torus knot `T(2,N)` is `N`: `A_N(-1) = N`. -/
theorem knot_determinant (N : ℕ) : (alexander N).eval (-1) = (N : ℤ) := by
  simp [alexander, eval_finset_sum, ← mul_pow]

/-- Alexander polynomials are normalized: `A_N(1) = 1` for odd `N`. -/
theorem alexander_eval_one {N : ℕ} (hN : Odd N) : (alexander N).eval 1 = 1 := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (X_add_one_mul_alexander_odd hN)
  simp at h
  omega

/-! ## Semiprimes -/

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

/-- **Semiprime factorization.** For distinct odd primes `p ≠ q` and `N = pq`,
`A_N = Φ_{2p} · Φ_{2q} · Φ_{2N}`. -/
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

/-! ## Degrees of the irreducible factors -/

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

/-- The three factors of `A_{pq}` have degrees `p-1`, `q-1`, `(p-1)(q-1)`,
and each is irreducible over `ℤ`. -/
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

/-- The degrees of the three factors sum to `deg A_{pq} = pq - 1`. -/
theorem alexander_semiprime_degree_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (p - 1) + (q - 1) + (p - 1) * (q - 1) = p * q - 1 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hp.one_lt.le
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hq.one_lt.le
  have h : (1 + a) * (1 + b) = 1 + (a + b + a * b) := by ring
  simp only [Nat.add_sub_cancel_left, h]

/-! ## Recovering the factorization from the degree data -/

/-- `φ(pq) = (p-1)(q-1)` and `p + q = pq + 1 - φ(pq)`. -/
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

/-- **Recovery.** From `N = pq` and the degree data (equivalently `φ(N)`), the primes are
recovered as the roots of `t² - s t + N` with `s = N + 1 - φ(N)`:
`p = (s - √(s²-4N))/2`, `q = (s + √(s²-4N))/2`. -/
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

/-! ## Irreducibility of `A_N` characterizes primality of `N` -/

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

/-- If `N` is odd, `> 1` and composite, then `A_N` factors as `Φ_{2d} · (rest)` with both
factors of positive degree, hence is reducible. -/
lemma alexander_not_irreducible_of_not_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N)
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

/-- **Primality detector.** For odd `N > 1`, the Alexander polynomial of `T(2,N)` is
irreducible over `ℤ` if and only if `N` is prime. -/
theorem alexander_irreducible_iff_prime {N : ℕ} (hN : Odd N) (h1 : 1 < N) :
    Irreducible (alexander N) ↔ N.Prime := by
  constructor
  · intro h
    by_contra hnp
    exact alexander_not_irreducible_of_not_prime hN h1 hnp h
  · intro hp
    rw [alexander_prime hN hp]
    exact cyclotomic.irreducible (by omega)

end Bridges.AlexanderTorus
-- ==== upstream: Packages/Catalog/Bridges/AlexanderKnotNumberBridgeIII.lean ====
/-
# The Knot–Number bridge, third cycle: divisibility, separability, duality

Three structural theorems about the Alexander polynomial `A_N` of the torus knot
`T(2,N)`, all consequences of the cyclotomic factorization proved in
`Bridges.AlexanderKnotNumberBridge`:

* `alexander_dvd_iff_dvd` : **the divisibility bridge**
  `A_d ∣ A_M ↔ d ∣ M` (odd `d, M > 1`).
  Divisibility of torus-knot Alexander polynomials is *exactly* divisibility of the
  knot parameters — the divisor lattice of `N` is faithfully encoded in the
  divisibility order of the polynomials.
* `alexander_separable_rat` / `alexander_squarefree_rat` : `A_N` is separable
  (hence squarefree) over `ℚ`: the `N-1` roots are pairwise distinct, so the
  Alexander module `ℚ[X]/(A_N)` is a product of `τ(N)-1` distinct cyclotomic fields.
* `alexander_reverse` : `A_N` is palindromic, `A_N.reverse = A_N`, the polynomial
  shadow of Poincaré duality for the knot complement.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisibility bridge -/

/-- `Φ_{2d}` divides `A_M` whenever `d ∣ M`, `d > 1`. -/
lemma cyclotomic_dvd_alexander {d M : ℕ} (hM : Odd M) (hM1 : 1 < M) (hdvd : d ∣ M)
    (hd1 : d ≠ 1) : cyclotomic (2 * d) ℤ ∣ alexander M := by
  have hmem : d ∈ M.divisors.erase 1 :=
    Finset.mem_erase.2 ⟨hd1, Nat.mem_divisors.2 ⟨hdvd, by omega⟩⟩
  rw [alexander_eq_prod_cyclotomic hM hM1]
  exact Finset.dvd_prod_of_mem _ hmem

/-- Easy direction: `d ∣ M` implies `A_d ∣ A_M`. -/
theorem alexander_dvd_of_dvd {d M : ℕ} (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (hdvd : d ∣ M) : alexander d ∣ alexander M := by
  have hd : Odd d := odd_of_dvd_odd hM hdvd
  rw [alexander_eq_prod_cyclotomic hd hd1, alexander_eq_prod_cyclotomic hM hM1]
  refine Finset.prod_dvd_prod_of_subset _ _ _ ?_
  intro e he
  obtain ⟨he1, hemem⟩ := Finset.mem_erase.1 he
  exact Finset.mem_erase.2
    ⟨he1, Nat.mem_divisors.2 ⟨(Nat.mem_divisors.1 hemem).1.trans hdvd, by omega⟩⟩

/-- If an irreducible monic polynomial divides another monic irreducible one, they are
equal. -/
lemma eq_of_monic_irreducible_dvd {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic)
    (hfi : Irreducible f) (hgi : Irreducible g) (h : f ∣ g) : f = g := by
  obtain ⟨c, hc⟩ := h
  rcases hgi.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu hfi.not_isUnit
  · have hcm : c.Monic := by
      have hlead := congrArg Polynomial.leadingCoeff hc
      rw [Polynomial.leadingCoeff_mul, hf.leadingCoeff, hg.leadingCoeff, one_mul] at hlead
      exact hlead.symm
    rw [hcm.eq_one_of_isUnit hu, mul_one] at hc
    exact hc.symm

/-- Hard direction: `A_d ∣ A_M` forces `d ∣ M`. -/
theorem dvd_of_alexander_dvd {d M : ℕ} (hd : Odd d) (hM : Odd M) (hd1 : 1 < d) (hM1 : 1 < M)
    (h : alexander d ∣ alexander M) : d ∣ M := by
  have hcyc : cyclotomic (2 * d) ℤ ∣ alexander M :=
    (cyclotomic_dvd_alexander hd hd1 dvd_rfl (by omega)).trans h
  have hirr : Irreducible (cyclotomic (2 * d) ℤ) := cyclotomic.irreducible (by omega)
  have hprime : Prime (cyclotomic (2 * d) ℤ) := irreducible_iff_prime.1 hirr
  rw [alexander_eq_prod_cyclotomic hM hM1] at hcyc
  obtain ⟨e, hemem, hdvd⟩ := hprime.exists_mem_finset_dvd hcyc
  obtain ⟨he1, hediv⟩ := Finset.mem_erase.1 hemem
  have hepos : 0 < e := Nat.pos_of_mem_divisors hediv
  have heq : cyclotomic (2 * d) ℤ = cyclotomic (2 * e) ℤ :=
    eq_of_monic_irreducible_dvd (cyclotomic.monic _ _) (cyclotomic.monic _ _) hirr
      (cyclotomic.irreducible (by omega)) hdvd
  have : 2 * d = 2 * e := cyclotomic_injective (R := ℤ) heq
  have hde : d = e := by omega
  rw [hde]
  exact (Nat.mem_divisors.1 hediv).1

/-- **The divisibility bridge.** For odd `d, M > 1`, the Alexander polynomial of
`T(2,d)` divides that of `T(2,M)` if and only if `d` divides `M`. -/
theorem alexander_dvd_iff_dvd {d M : ℕ} (hd : Odd d) (hM : Odd M) (hd1 : 1 < d)
    (hM1 : 1 < M) : alexander d ∣ alexander M ↔ d ∣ M :=
  ⟨dvd_of_alexander_dvd hd hM hd1 hM1, alexander_dvd_of_dvd hM hd1 hM1⟩

/-! ## Separability: the `N-1` roots are distinct -/

/-- `A_N` divides `X^{2N} - 1` (over any commutative ring), for odd `N`. -/
lemma alexander_dvd_X_pow_sub_one {N : ℕ} (hN : Odd N) :
    alexander N ∣ (X : ℤ[X]) ^ (2 * N) - 1 := by
  refine ⟨(X + 1) * ((X : ℤ[X]) ^ N - 1), ?_⟩
  have h := X_add_one_mul_alexander_odd hN
  have hX : ((X : ℤ[X]) ^ (2 * N) - 1) = ((X ^ N + 1) * (X ^ N - 1)) := by
    rw [two_mul, pow_add]; ring
  rw [hX, ← h]; ring

/-- Over `ℚ`, the Alexander polynomial of `T(2,N)` is separable: its `N-1` complex roots
are pairwise distinct. -/
theorem alexander_separable_rat {N : ℕ} (hN : Odd N) :
    ((alexander N).map (Int.castRingHom ℚ)).Separable := by
  have hpos : 0 < N := hN.pos
  have hsep : ((X : ℚ[X]) ^ (2 * N) - C 1).Separable := by
    refine separable_X_pow_sub_C (1 : ℚ) ?_ one_ne_zero
    have : (0 : ℚ) < (2 * N : ℕ) := by positivity
    exact_mod_cast this.ne'
  refine hsep.of_dvd ?_
  have hdvd := alexander_dvd_X_pow_sub_one hN
  have := Polynomial.map_dvd (Int.castRingHom ℚ) hdvd
  simpa using this

/-- Consequently `A_N` is squarefree over `ℚ`: the Alexander module `ℚ[X]/(A_N)` is a
product of distinct cyclotomic fields. -/
theorem alexander_squarefree_rat {N : ℕ} (hN : Odd N) :
    Squarefree ((alexander N).map (Int.castRingHom ℚ)) :=
  (alexander_separable_rat hN).squarefree

/-! ## Palindromicity (Poincaré duality shadow) -/

lemma reverse_X_pow_add_one {N : ℕ} (hpos : 0 < N) :
    ((X : ℤ[X]) ^ N + 1).reverse = (X : ℤ[X]) ^ N + 1 := by
  have hdeg : ((X : ℤ[X]) ^ N + 1).natDegree = N := by
    have hC : ((X : ℤ[X]) ^ N + 1) = (X ^ N + C 1) := by simp
    rw [hC, natDegree_X_pow_add_C]
  ext n
  rw [coeff_reverse, hdeg]
  rcases le_or_gt n N with h | h
  · rw [revAt_le h]
    simp only [coeff_add, coeff_X_pow, coeff_one]
    have h1 : (N - n = N) ↔ (n = 0) := by omega
    have h2 : (N - n = 0) ↔ (n = N) := by omega
    by_cases hn0 : n = 0
    · subst hn0; simp [hpos.ne, hpos.ne']
    · by_cases hnN : n = N
      · subst hnN; simp [hpos.ne, hpos.ne']
      · rw [if_neg (by omega), if_neg (by omega), if_neg hnN, if_neg hn0]
  · rw [revAt_eq_self_of_lt h]

/-- **Palindromicity.** `A_N` is its own reverse: the coefficient sequence
`1, -1, 1, …, 1` is symmetric. This is the polynomial shadow of the duality
`Δ(t) ≐ Δ(t⁻¹)` satisfied by Alexander polynomials of knots. -/
theorem alexander_reverse {N : ℕ} (hN : Odd N) : (alexander N).reverse = alexander N := by
  have hpos : 0 < N := hN.pos
  have h := X_add_one_mul_alexander_odd hN
  have hrev := congrArg Polynomial.reverse h
  rw [reverse_mul_of_domain, reverse_X_pow_add_one hpos] at hrev
  have hX1 : ((X : ℤ[X]) + 1).reverse = X + 1 := by
    have := reverse_X_pow_add_one (N := 1) one_pos
    simpa using this
  rw [hX1, ← h] at hrev
  have hne : (X + 1 : ℤ[X]) ≠ 0 := fun hc => by
    simpa using congrArg (Polynomial.eval 0) hc
  exact mul_left_cancel₀ hne hrev

end Bridges.AlexanderTorus
-- ==== upstream: Packages/Catalog/Bridges/AlexanderKnotNumberBridgeIV.lean ====
/-
# The Knot–Number bridge, fourth cycle: coprimality and the size obstruction

Two final structural results.

* **Coprimality bridge** (`alexander_common_divisors_unit_iff_coprime`):
  for odd `M, N > 1`, *every* common divisor of `A_M` and `A_N` in `ℤ[X]` is a unit
  **iff** `gcd(M, N) = 1`. Together with `alexander_dvd_iff_dvd` of cycle III this
  says the map `N ↦ A_N` is an embedding of the divisibility lattice of odd numbers
  into the divisibility lattice of `ℤ[X]`.

* **The size obstruction** (`alexander_support_card`, `alexander_coeff`):
  every one of the `N` coefficients of `A_N` is `±1`, so `A_N` has exactly `N`
  nonzero terms. Writing `A_N` down costs `Θ(N) = Θ(exp(log N))` — this is the
  precise sense in which the bridge is *not* a factoring algorithm.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Coefficients: the size obstruction -/

theorem alexander_coeff (N i : ℕ) :
    (alexander N).coeff i = if i < N then (-1 : ℤ) ^ i else 0 := by
  induction N with
  | zero => simp
  | succ n ih =>
      have hterm : ((-1 : ℤ[X]) ^ n * X ^ n).coeff i = if i = n then (-1 : ℤ) ^ n else 0 := by
        rw [show ((-1 : ℤ[X]) ^ n) = C ((-1 : ℤ) ^ n) by simp [map_pow], coeff_C_mul,
          coeff_X_pow]
        split <;> simp_all
      rw [alexander_succ, coeff_add, ih, hterm]
      rcases lt_trichotomy i n with h | h | h
      · rw [if_pos h, if_neg (by omega), if_pos (by omega), add_zero]
      · subst h
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega), zero_add]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]

/-- Every coefficient of `A_N` below the degree is `±1`, hence nonzero: the support of
`A_N` is all of `{0, …, N-1}`. -/
theorem alexander_support (N : ℕ) : (alexander N).support = Finset.range N := by
  ext i
  rw [Polynomial.mem_support_iff, alexander_coeff, Finset.mem_range]
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact h rfl
  · intro h
    rw [if_pos h]
    exact pow_ne_zero i (by norm_num)

/-- **The size obstruction.** `A_N` has exactly `N` nonzero coefficients, all `±1`. -/
theorem alexander_support_card (N : ℕ) : (alexander N).support.card = N := by
  rw [alexander_support, Finset.card_range]

/-! ## Coprimality bridge -/

/-- If an irreducible `p` divides `A_M` (`M` odd `> 1`), then `p` is associated to
`Φ_{2d}` for some divisor `d > 1` of `M`. -/
lemma exists_divisor_of_irreducible_dvd_alexander {M : ℕ} (hM : Odd M) (hM1 : 1 < M)
    {p : ℤ[X]} (hp : Irreducible p) (hdvd : p ∣ alexander M) :
    ∃ d, d ∣ M ∧ 1 < d ∧ Associated p (cyclotomic (2 * d) ℤ) := by
  have hprime : Prime p := irreducible_iff_prime.1 hp
  rw [alexander_eq_prod_cyclotomic hM hM1] at hdvd
  obtain ⟨d, hdmem, hdvd'⟩ := hprime.exists_mem_finset_dvd hdvd
  obtain ⟨hd1, hddiv⟩ := Finset.mem_erase.1 hdmem
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hddiv
  exact ⟨d, (Nat.mem_divisors.1 hddiv).1, by omega,
    hp.associated_of_dvd (cyclotomic.irreducible (by omega)) hdvd'⟩

/-- **Coprimality bridge.** For odd `M, N > 1`: the Alexander polynomials of `T(2,M)`
and `T(2,N)` have only unit common divisors iff `M` and `N` are coprime. -/
theorem alexander_common_divisors_unit_iff_coprime {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hM1 : 1 < M) (hN1 : 1 < N) :
    (∀ f : ℤ[X], f ∣ alexander M → f ∣ alexander N → IsUnit f) ↔ Nat.Coprime M N := by
  constructor
  · intro h
    by_contra hcop
    obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd M N := ⟨_, rfl⟩
    have hgM : g ∣ M := hgdef ▸ Nat.gcd_dvd_left M N
    have hgN : g ∣ N := hgdef ▸ Nat.gcd_dvd_right M N
    have hg1 : 1 < g := by
      have hgpos : 0 < g := hgdef ▸ Nat.gcd_pos_of_pos_left N (by omega)
      have hgne : g ≠ 1 := fun hc => hcop (hgdef.symm.trans hc)
      omega
    have hgodd : Odd g := odd_of_dvd_odd hM hgM
    have hu := h (alexander g) (alexander_dvd_of_dvd hM hg1 hM1 hgM)
      (alexander_dvd_of_dvd hN hg1 hN1 hgN)
    have hdeg : 0 < (alexander g).natDegree := by
      rw [alexander_natDegree hgodd]; omega
    exact (Polynomial.not_isUnit_of_natDegree_pos _ hdeg) hu
  · intro hcop f hfM hfN
    by_contra hnu
    have hf0 : f ≠ 0 := by
      rintro rfl
      exact alexander_ne_zero hM (zero_dvd_iff.1 hfM)
    obtain ⟨p, hp, hpf⟩ := WfDvdMonoid.exists_irreducible_factor hnu hf0
    obtain ⟨d, hdM, hd1, hpd⟩ :=
      exists_divisor_of_irreducible_dvd_alexander hM hM1 hp (hpf.trans hfM)
    obtain ⟨e, heN, he1, hpe⟩ :=
      exists_divisor_of_irreducible_dvd_alexander hN hN1 hp (hpf.trans hfN)
    have hassoc : Associated (cyclotomic (2 * d) ℤ) (cyclotomic (2 * e) ℤ) :=
      hpd.symm.trans hpe
    have heq : cyclotomic (2 * d) ℤ = cyclotomic (2 * e) ℤ :=
      eq_of_monic_irreducible_dvd (cyclotomic.monic _ _) (cyclotomic.monic _ _)
        (cyclotomic.irreducible (by omega)) (cyclotomic.irreducible (by omega)) hassoc.dvd
    have hde : d = e := by
      have := cyclotomic_injective (R := ℤ) heq
      omega
    subst hde
    have hdvd1 : d ∣ 1 := hcop ▸ Nat.dvd_gcd hdM heN
    have : d ≤ 1 := Nat.le_of_dvd one_pos hdvd1
    omega

end Bridges.AlexanderTorus
-- ==== upstream: Packages/Catalog/Bridges/AlexanderKnotNumberBridgeVII.lean ====
/-
# The knot–number bridge VII: the divisor lattice, gcd's and the failure of lcm's

Cycle III proved the *poset* statement `A_d ∣ A_M ↔ d ∣ M` and cycle IV the coprimality
statement "all common divisors of `A_M`, `A_N` are units iff `gcd(M,N) = 1`".  Conjecture `C4`
of `FUTURE_DIRECTIONS.md` asked whether `N ↦ A_N` is a lattice map, i.e. whether
`gcd(A_M, A_N) ≐ A_{gcd(M,N)}` **and** `lcm(A_M, A_N) ≐ A_{lcm(M,N)}`.

This file settles both halves:

* `Bridges.AlexanderTorus.alexander_gcd` : the gcd half is **true** — for odd `M, N > 0`,
  `gcd(A_M, A_N)` is associated to `A_{gcd(M,N)}` in `ℤ[X]`, with the universal-property
  form `alexander_dvd_gcd_of_dvd_of_dvd`.
* `Bridges.AlexanderTorus.alexander_lcm_not_associated` : the lcm half is **false** — already
  `lcm(A_3, A_5)` has degree `6` while `A_{15}` has degree `14`, so the map `N ↦ A_N` is a
  meet-morphism but not a join-morphism of the divisor lattice.

The mechanism behind the gcd half is that `A_M` is a product of *distinct* cyclotomic primes
`Φ_{2d}`, `d ∣ M`, `d > 1`, so the "excess" parts of `A_M` and `A_N` over `A_{gcd(M,N)}`
share no irreducible factor; the mechanism behind the failure of the lcm half is that
`A_{lcm(M,N)}` also contains the factors `Φ_{2d}` for divisors `d` of `lcm(M,N)` that divide
neither `M` nor `N`.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## The divisor-product formula, including `N = 1` -/

/-- `A_N = ∏_{d ∣ N, d > 1} Φ_{2d}` for every odd `N > 0` (the case `N = 1` reads `1 = 1`). -/
lemma alexander_eq_prod_cyclotomic_of_pos {N : ℕ} (hN : Odd N) (hpos : 0 < N) :
    alexander N = ∏ d ∈ N.divisors.erase 1, cyclotomic (2 * d) ℤ := by
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.2 hpos.ne') with h1 | h1
  · rw [← h1]
    simp [alexander]
  · exact alexander_eq_prod_cyclotomic hN h1

lemma divisors_erase_one_subset {G M : ℕ} (hGM : G ∣ M) (hM : 0 < M) :
    G.divisors.erase 1 ⊆ M.divisors.erase 1 := by
  intro d hd
  rw [Finset.mem_erase, Nat.mem_divisors] at hd ⊢
  exact ⟨hd.1, hd.2.1.trans hGM, hM.ne'⟩

/-- The "excess" factor of `A_M` over `A_G` for a divisor `G ∣ M`. -/
-- [dropped: platform already declares excess]
lemma alexander_eq_mul_excess {G M : ℕ} (hM : Odd M) (hMpos : 0 < M) (hGM : G ∣ M)
    (hGpos : 0 < G) : alexander M = alexander G * excess G M := by
  have hG : Odd G := odd_of_dvd_odd hM hGM
  rw [alexander_eq_prod_cyclotomic_of_pos hM hMpos,
    alexander_eq_prod_cyclotomic_of_pos hG hGpos, excess,
    mul_comm, Finset.prod_sdiff (divisors_erase_one_subset hGM hMpos)]

lemma excess_ne_zero (G M : ℕ) : excess G M ≠ 0 := by
  rw [excess]
  refine Finset.prod_ne_zero_iff.2 ?_
  intro d _
  exact cyclotomic_ne_zero _ ℤ

/-! ## The two excesses share no irreducible factor -/

/-- The excess of `A_M` and the excess of `A_N` over `A_{gcd(M,N)}` are relatively prime:
any common divisor is a unit. -/
theorem isRelPrime_excess {M N : ℕ} (hMpos : 0 < M) (hNpos : 0 < N) :
    IsRelPrime (excess (Nat.gcd M N) M) (excess (Nat.gcd M N) N) := by
  set G := Nat.gcd M N with hG
  intro c hcM hcN
  by_contra hnu
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact excess_ne_zero G M (zero_dvd_iff.1 hcM)
  obtain ⟨p, hp, hpc⟩ := WfDvdMonoid.exists_irreducible_factor hnu hc0
  have hprime : Prime p := irreducible_iff_prime.1 hp
  have hpM : p ∣ excess G M := hpc.trans hcM
  have hpN : p ∣ excess G N := hpc.trans hcN
  rw [excess] at hpM hpN
  obtain ⟨d, hdmem, hpd⟩ := hprime.exists_mem_finset_dvd hpM
  obtain ⟨e, hemem, hpe⟩ := hprime.exists_mem_finset_dvd hpN
  rw [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors] at hdmem hemem
  obtain ⟨⟨hd1, hdM, -⟩, hdG⟩ := hdmem
  obtain ⟨⟨he1, heN, -⟩, -⟩ := hemem
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdM hMpos
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos heN hNpos
  -- `p` is associated to both `Φ_{2d}` and `Φ_{2e}`, hence `d = e`
  have hassoc : Associated p (cyclotomic (2 * d) ℤ) :=
    hp.associated_of_dvd (cyclotomic.irreducible (by omega)) hpd
  have hdvd : cyclotomic (2 * d) ℤ ∣ cyclotomic (2 * e) ℤ := hassoc.symm.dvd.trans hpe
  have heq : cyclotomic (2 * d) ℤ = cyclotomic (2 * e) ℤ :=
    eq_of_monic_irreducible_dvd (cyclotomic.monic _ _) (cyclotomic.monic _ _)
      (cyclotomic.irreducible (by omega)) (cyclotomic.irreducible (by omega)) hdvd
  have h2 : 2 * d = 2 * e := cyclotomic_injective (R := ℤ) heq
  have hde : d = e := by omega
  -- but then `d` divides both `M` and `N`, so `d ∈ G.divisors.erase 1`: contradiction
  refine hdG ?_
  rw [Finset.mem_erase, Nat.mem_divisors]
  exact ⟨hd1, Nat.dvd_gcd hdM (hde ▸ heN), Nat.gcd_pos_of_pos_left N hMpos |>.ne'⟩

/-! ## The gcd half of the lattice conjecture: true -/

/-- **Meet morphism.** For odd `M, N > 0`, `gcd(A_M, A_N)` is associated to `A_{gcd(M,N)}`. -/
theorem alexander_gcd {M N : ℕ} (hM : Odd M) (hN : Odd N) (hMpos : 0 < M) (hNpos : 0 < N) :
    Associated (gcd (alexander M) (alexander N)) (alexander (Nat.gcd M N)) := by
  set G := Nat.gcd M N with hG
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_left N hMpos
  have hGM : G ∣ M := Nat.gcd_dvd_left M N
  have hGN : G ∣ N := Nat.gcd_dvd_right M N
  have hu : IsUnit (gcd (excess G M) (excess G N)) :=
    isRelPrime_excess hMpos hNpos (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  rw [alexander_eq_mul_excess hM hMpos hGM hGpos, alexander_eq_mul_excess hN hNpos hGN hGpos,
    _root_.gcd_mul_left]
  exact (associated_mul_unit_left _ _ hu).trans (normalize_associated _)

/-- Universal-property form of the meet morphism: every common divisor of `A_M` and `A_N`
divides `A_{gcd(M,N)}`. -/
theorem alexander_dvd_gcd_of_dvd_of_dvd {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) {c : ℤ[X]} (hcM : c ∣ alexander M) (hcN : c ∣ alexander N) :
    c ∣ alexander (Nat.gcd M N) :=
  (dvd_gcd hcM hcN).trans (alexander_gcd hM hN hMpos hNpos).dvd

/-! ## The lcm half of the lattice conjecture: false -/

lemma natDegree_eq_of_associated {f g : ℤ[X]} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : Associated f g) : f.natDegree = g.natDegree :=
  le_antisymm (natDegree_le_of_dvd h.dvd hg) (natDegree_le_of_dvd h.symm.dvd hf)

lemma associated_lcm_three_five :
    Associated (lcm (alexander 3) (alexander 5)) (alexander 3 * alexander 5) := by
  have hu : IsUnit (gcd (alexander 3) (alexander 5)) := by
    refine (alexander_common_divisors_unit_iff_coprime (by decide) (by decide)
      (by norm_num) (by norm_num)).2 (by decide) _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  refine ((associated_unit_mul_left (lcm (alexander 3) (alexander 5)) _ hu).symm.trans ?_)
  exact gcd_mul_lcm _ _

/-- **No join morphism.** `lcm(A_3, A_5)` is *not* associated to `A_{lcm(3,5)} = A_{15}`:
the former has degree `6` (it is `Φ_6 · Φ_10`), the latter degree `14` (it also contains
the factor `Φ_30`).  This refutes the lcm half of the lattice conjecture. -/
theorem alexander_lcm_not_associated :
    ¬ Associated (lcm (alexander 3) (alexander 5)) (alexander (Nat.lcm 3 5)) := by
  have h3 : (alexander 3).natDegree = 2 := alexander_natDegree (by decide)
  have h5 : (alexander 5).natDegree = 4 := alexander_natDegree (by decide)
  have h15 : (alexander 15).natDegree = 14 := alexander_natDegree (by decide)
  have h3ne : alexander 3 ≠ 0 := alexander_ne_zero (by decide)
  have h5ne : alexander 5 ≠ 0 := alexander_ne_zero (by decide)
  have h15ne : alexander 15 ≠ 0 := alexander_ne_zero (by decide)
  have hprodne : alexander 3 * alexander 5 ≠ 0 := mul_ne_zero h3ne h5ne
  have hlcmne : lcm (alexander 3) (alexander 5) ≠ 0 := by
    intro h
    have hass := associated_lcm_three_five
    rw [h] at hass
    exact hprodne (hass.eq_zero_iff.1 rfl)
  have hdeg : (lcm (alexander 3) (alexander 5)).natDegree = 6 := by
    rw [natDegree_eq_of_associated hlcmne hprodne associated_lcm_three_five,
      natDegree_mul h3ne h5ne, h3, h5]
  intro hassoc
  have hlcm : Nat.lcm 3 5 = 15 := by decide
  rw [hlcm] at hassoc
  have := natDegree_eq_of_associated hlcmne h15ne hassoc
  rw [hdeg, h15] at this
  exact absurd this (by norm_num)

end Bridges.AlexanderTorus
-- ==== upstream: Packages/Catalog/Bridges/AlexanderKnotNumberBridgeXI.lean ====
/-
# The knot–number bridge XI: the join defect

Cycle VII proved that `N ↦ A_N` is a **meet**-morphism of the divisor lattice
(`alexander_gcd`) but *not* a join-morphism (`alexander_lcm_not_associated`).  Conjecture
`D1` of `FUTURE_DIRECTIONS.md` asked for the exact size of the failure.  This file closes it.

* `Bridges.AlexanderTorus.alexander_lcm_eq_joinProd` : for odd `M, N > 0`,
  `lcm(A_M, A_N)` is associated to `∏_{d ∣ M or d ∣ N, d > 1} Φ_{2d}` — the join on the
  polynomial side is the product over the *union* of the two divisor sets, whereas
  `A_{lcm(M,N)}` is the product over the divisor set of `lcm(M,N)`, which is generally larger.
* `Bridges.AlexanderTorus.alexander_lcm_mul_joinDefect` : the missing factor is exactly
  `∏_{d ∣ lcm(M,N), d ∤ M, d ∤ N, d > 1} Φ_{2d}`, and
  `Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect` measures it:
  `deg A_{lcm(M,N)} = deg lcm(A_M, A_N) + ∑_{d} φ(d)` over that same index set.
* `Bridges.AlexanderTorus.joinDefect_isUnit_iff` : the join morphism property holds at
  `(M, N)` precisely when `lcm(M,N)` has no divisor `> 1` outside `divisors M ∪ divisors N`.
* `Bridges.AlexanderTorus.joinDefect_three_five_natDegree` : the numerical instance behind
  cycle VII's counterexample — the defect for `(3,5)` is `Φ_30`, of degree `φ(15) = 8`,
  and indeed `14 = 6 + 8`.

Everything reduces, as predicted, to the Finset identity
`(∏_{s ∪ t}) · (∏_{s ∩ t}) = (∏_s) · (∏_t)` together with `divisors (gcd M N) =
divisors M ∩ divisors N`.
-/

namespace Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Divisor sets of gcd's and lcm's -/

/-- The divisors of `gcd M N` are exactly the common divisors of `M` and `N`. -/
lemma divisors_gcd {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    (Nat.gcd M N).divisors = M.divisors ∩ N.divisors := by
  ext d
  simp only [Finset.mem_inter, Nat.mem_divisors]
  constructor
  · rintro ⟨hd, -⟩
    exact ⟨⟨hd.trans (Nat.gcd_dvd_left M N), hM.ne'⟩,
      ⟨hd.trans (Nat.gcd_dvd_right M N), hN.ne'⟩⟩
  · rintro ⟨⟨h1, -⟩, h2, -⟩
    exact ⟨Nat.dvd_gcd h1 h2, (Nat.gcd_pos_of_pos_left N hM).ne'⟩

/-- The index set of the join: the nontrivial divisors of `M` together with those of `N`. -/
-- [dropped: platform already declares unionIdx]
lemma mem_unionIdx {M N d : ℕ} :
    d ∈ unionIdx M N ↔ d ≠ 1 ∧ (d ∣ M ∧ M ≠ 0 ∨ d ∣ N ∧ N ≠ 0) := by
  simp [unionIdx, Finset.mem_erase, Nat.mem_divisors]

/-- The cyclotomic product over the union of the two divisor sets. -/
-- [dropped: platform already declares joinProd]
lemma joinProd_ne_zero (M N : ℕ) : joinProd M N ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ _ => cyclotomic_ne_zero _ ℤ

/-- The multiplicative form of inclusion–exclusion on the divisor lattice:
`(join) · A_{gcd(M,N)} = A_M · A_N`. -/
lemma joinProd_mul_alexander_gcd {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    joinProd M N * alexander (Nat.gcd M N) = alexander M * alexander N := by
  have hGpos : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left N hMpos
  have hG : Odd (Nat.gcd M N) := odd_of_dvd_odd hM (Nat.gcd_dvd_left M N)
  have hinter : (Nat.gcd M N).divisors.erase 1
      = (M.divisors.erase 1) ∩ (N.divisors.erase 1) := by
    rw [divisors_gcd hMpos hNpos]
    ext x
    simp only [Finset.mem_erase, Finset.mem_inter]
    tauto
  rw [alexander_eq_prod_cyclotomic_of_pos hM hMpos,
    alexander_eq_prod_cyclotomic_of_pos hN hNpos,
    alexander_eq_prod_cyclotomic_of_pos hG hGpos, hinter, joinProd, unionIdx,
    Finset.erase_union_distrib]
  exact Finset.prod_union_inter (f := fun d => cyclotomic (2 * d) ℤ)

/-! ## The join on the polynomial side -/

/-- **The join is the product over the union of the divisor sets.**  For odd `M, N > 0`,
`lcm(A_M, A_N) ≐ ∏_{d ∣ M or d ∣ N, d > 1} Φ_{2d}`. -/
theorem alexander_lcm_eq_joinProd {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    Associated (lcm (alexander M) (alexander N)) (joinProd M N) := by
  set G := Nat.gcd M N with hGdef
  have hGpos : 0 < G := Nat.gcd_pos_of_pos_left N hMpos
  have hG : Odd G := odd_of_dvd_odd hM (Nat.gcd_dvd_left M N)
  have hGne : alexander G ≠ 0 := alexander_ne_zero hG
  -- `gcd · lcm ≐ A_M · A_N = joinProd · A_G`
  have h1 : Associated (gcd (alexander M) (alexander N) * lcm (alexander M) (alexander N))
      (alexander M * alexander N) := gcd_mul_lcm _ _
  have hassocG : Associated (alexander G) (gcd (alexander M) (alexander N)) :=
    (alexander_gcd hM hN hMpos hNpos).symm
  have h2 : Associated (alexander G * lcm (alexander M) (alexander N))
      (joinProd M N * alexander G) := by
    have h := (hassocG.mul_right (lcm (alexander M) (alexander N))).trans h1
    rwa [← joinProd_mul_alexander_gcd hM hN hMpos hNpos] at h
  -- cancel the nonzero factor `A_G`
  have h3 : Associated (lcm (alexander M) (alexander N) * alexander G)
      (joinProd M N * alexander G) := by
    rwa [mul_comm (alexander G)] at h2
  exact h3.of_mul_right (Associated.refl _) hGne

/-! ## The join defect -/

/-- The join defect: the cyclotomic factors of `A_{lcm(M,N)}` that are visible at neither
`M` nor `N`. -/
-- [dropped: platform already declares joinDefect]
lemma unionIdx_subset_lcm {M N : ℕ} (hMpos : 0 < M) (hNpos : 0 < N) :
    unionIdx M N ⊆ (Nat.lcm M N).divisors.erase 1 := by
  intro d hd
  rw [mem_unionIdx] at hd
  have hlcm : Nat.lcm M N ≠ 0 := Nat.pos_of_ne_zero (fun h => by
    simp [Nat.lcm_eq_zero_iff, hMpos.ne', hNpos.ne'] at h) |>.ne'
  rw [Finset.mem_erase, Nat.mem_divisors]
  refine ⟨hd.1, ?_, hlcm⟩
  rcases hd.2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact h.trans (Nat.dvd_lcm_left M N)
  · exact h.trans (Nat.dvd_lcm_right M N)

/-- **The exact join defect.**  `A_{lcm(M,N)} = (join) · (defect)`, where the defect is the
product of the `Φ_{2d}` over the divisors `d > 1` of `lcm(M,N)` dividing neither `M` nor `N`. -/
theorem alexander_lcm_mul_joinDefect {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    alexander (Nat.lcm M N) = joinProd M N * joinDefect M N := by
  have hLpos : 0 < Nat.lcm M N := Nat.pos_of_ne_zero (fun h => by
    simp [Nat.lcm_eq_zero_iff, hMpos.ne', hNpos.ne'] at h)
  have hL : Odd (Nat.lcm M N) := by
    rcases hM with ⟨a, ha⟩
    rcases hN with ⟨b, hb⟩
    refine Nat.odd_iff.2 ?_
    have h2 : ¬ (2 ∣ Nat.lcm M N) := by
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2.trans (Nat.lcm_dvd_mul M N)) with h | h
      · omega
      · omega
    omega
  rw [alexander_eq_prod_cyclotomic_of_pos hL hLpos, joinProd, joinDefect,
    ← Finset.prod_sdiff (unionIdx_subset_lcm hMpos hNpos)]
  exact mul_comm _ _

/-- Corollary: the polynomial join always divides the Alexander polynomial of the lattice
join, but (cycle VII) need not equal it. -/
theorem lcm_alexander_dvd_alexander_lcm {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    lcm (alexander M) (alexander N) ∣ alexander (Nat.lcm M N) := by
  refine (alexander_lcm_eq_joinProd hM hN hMpos hNpos).dvd.trans ?_
  exact ⟨joinDefect M N, alexander_lcm_mul_joinDefect hM hN hMpos hNpos⟩

/-! ## Degrees -/

lemma natDegree_prod_cyclotomic_two_mul {s : Finset ℕ} (hodd : ∀ d ∈ s, Odd d) :
    (∏ d ∈ s, cyclotomic (2 * d) ℤ).natDegree = ∑ d ∈ s, Nat.totient d := by
  rw [natDegree_prod _ _ (fun d _ => cyclotomic_ne_zero _ ℤ)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [natDegree_cyclotomic, totient_two_mul_of_odd (hodd d hd)]

lemma joinProd_natDegree {M N : ℕ} (hM : Odd M) (hN : Odd N) :
    (joinProd M N).natDegree = ∑ d ∈ unionIdx M N, Nat.totient d := by
  refine natDegree_prod_cyclotomic_two_mul fun d hd => ?_
  rw [mem_unionIdx] at hd
  rcases hd.2 with ⟨h, -⟩ | ⟨h, -⟩
  · exact odd_of_dvd_odd hM h
  · exact odd_of_dvd_odd hN h

lemma joinDefect_natDegree {M N : ℕ} (hM : Odd M) (hN : Odd N) :
    (joinDefect M N).natDegree
      = ∑ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, Nat.totient d := by
  have hL : Odd (Nat.lcm M N) := by
    rcases hM with ⟨a, ha⟩
    rcases hN with ⟨b, hb⟩
    refine Nat.odd_iff.2 ?_
    have h2 : ¬ (2 ∣ Nat.lcm M N) := by
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2.trans (Nat.lcm_dvd_mul M N)) with h | h
      · omega
      · omega
    omega
  refine natDegree_prod_cyclotomic_two_mul fun d hd => ?_
  rw [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors] at hd
  exact odd_of_dvd_odd hL hd.1.2.1

/-- **Quantitative failure of the join morphism.**  The degree gap between `A_{lcm(M,N)}` and
`lcm(A_M, A_N)` is exactly `∑ φ(d)` over the divisors `d > 1` of `lcm(M,N)` that divide
neither `M` nor `N`. -/
theorem alexander_lcm_natDegree_add_defect {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    (alexander (Nat.lcm M N)).natDegree
      = (lcm (alexander M) (alexander N)).natDegree
        + ∑ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, Nat.totient d := by
  have hlcmne : lcm (alexander M) (alexander N) ≠ 0 := by
    intro h
    have := (alexander_lcm_eq_joinProd hM hN hMpos hNpos)
    rw [h] at this
    exact joinProd_ne_zero M N (this.eq_zero_iff.1 rfl)
  have hdeg : (lcm (alexander M) (alexander N)).natDegree = (joinProd M N).natDegree :=
    natDegree_eq_of_associated hlcmne (joinProd_ne_zero M N)
      (alexander_lcm_eq_joinProd hM hN hMpos hNpos)
  rw [hdeg, alexander_lcm_mul_joinDefect hM hN hMpos hNpos,
    natDegree_mul (joinProd_ne_zero M N) (by
      exact Finset.prod_ne_zero_iff.2 fun d _ => cyclotomic_ne_zero _ ℤ),
    joinDefect_natDegree hM hN]

/-- The join morphism property holds at `(M,N)` **iff** `lcm(M,N)` has no divisor `> 1`
beyond those of `M` and of `N`. -/
theorem joinDefect_isUnit_iff {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    IsUnit (joinDefect M N)
      ↔ ∀ d, d ∣ Nat.lcm M N → d ≠ 1 → d ∣ M ∨ d ∣ N := by
  have hL : Odd (Nat.lcm M N) := by
    rcases hM with ⟨a, ha⟩
    rcases hN with ⟨b, hb⟩
    refine Nat.odd_iff.2 ?_
    have h2 : ¬ (2 ∣ Nat.lcm M N) := by
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2.trans (Nat.lcm_dvd_mul M N)) with h | h
      · omega
      · omega
    omega
  have hLpos : 0 < Nat.lcm M N := Nat.pos_of_ne_zero (fun h => by
    simp [Nat.lcm_eq_zero_iff, hMpos.ne', hNpos.ne'] at h)
  constructor
  · intro hu d hdL hd1
    by_contra hcon
    push_neg at hcon
    have hnotmem : d ∉ unionIdx M N := by
      rw [mem_unionIdx]
      rintro ⟨-, ⟨hdm, -⟩ | ⟨hdn, -⟩⟩
      · exact hcon.1 hdm
      · exact hcon.2 hdn
    have hmem : d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N :=
      Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hd1, Nat.mem_divisors.2 ⟨hdL, hLpos.ne'⟩⟩, hnotmem⟩
    -- a cyclotomic factor of the defect is not a unit
    have hdvd : cyclotomic (2 * d) ℤ ∣ joinDefect M N := Finset.dvd_prod_of_mem _ hmem
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL hLpos
    have : IsUnit (cyclotomic (2 * d) ℤ) := isUnit_of_dvd_unit hdvd hu
    exact (cyclotomic.irreducible (n := 2 * d) (by omega)).not_isUnit this
  · intro h
    have hempty : ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun d hd => ?_
      rw [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors, mem_unionIdx] at hd
      obtain ⟨⟨hd1, hdL, -⟩, hnot⟩ := hd
      refine hnot ⟨hd1, ?_⟩
      rcases h d hdL hd1 with hdm | hdn
      · exact Or.inl ⟨hdm, hMpos.ne'⟩
      · exact Or.inr ⟨hdn, hNpos.ne'⟩
    rw [joinDefect, hempty, Finset.prod_empty]
    exact isUnit_one

/-! ## The numerical instance behind cycle VII's counterexample -/

/-- For `(M,N) = (3,5)` the defect is `Φ_30`, of degree `φ(15) = 8`; together with
`deg lcm(A_3,A_5) = 6` this reproves `14 = 6 + 8`, i.e. cycle VII's
`alexander_lcm_not_associated`, now with the exact size of the gap. -/
theorem joinDefect_three_five_natDegree : (joinDefect 3 5).natDegree = 8 := by
  have h : (joinDefect 3 5).natDegree
      = ∑ d ∈ ((Nat.lcm 3 5).divisors.erase 1) \ unionIdx 3 5, Nat.totient d :=
    joinDefect_natDegree (by decide) (by decide)
  rw [h]
  decide

end Bridges.AlexanderTorus
section
open Bridges.AlexanderTorus
open Polynomial Finset

theorem solution {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    (alexander (Nat.lcm M N)).natDegree
      = (lcm (alexander M) (alexander N)).natDegree
        + ∑ d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N, Nat.totient d := by
  first
  | exact Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect hM hN hMpos hNpos
  | exact Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect
  | exact @Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect M N hM hN hMpos hNpos
  | apply Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect
  | exact Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect ..


end
