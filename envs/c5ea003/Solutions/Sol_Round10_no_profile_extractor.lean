-- Prove2me | solution 1 for Round10.no_profile_extractor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:55:36.680302+00:00
-- url     : https://prove2.me/submissions/6b7f8447-e197-4080-8237-f210919d71df

-- Sol generated from Geometry/Round10Closures/JointClosure.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_JointClosure
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_eq
/-
Round-10 Closures — Part II: joint closure of the free-witness classification.

Experiment 337 (JOINTCLOSURE) asked whether *joints* of partial free witnesses
close on the factorisation: given a finite set `S` of exponents, does the vector
`(R_k(N))_{k ∈ S}` determine `p` and `q`?

The answer proved here is a definitive **no**, and the proof is analytic:
Dirichlet's theorem on primes in arithmetic progressions produces infinitely many
primes `p ≡ 1 (mod ∏_{k∈S} k)`, all of which *saturate* every witness in `S`
(`gcd(p-1,k) = k`).  Hence the whole joint profile is constant along an infinite
family of pairwise distinct semiprimes: persistent collisions, no aggregation
channel, and no profile-reading extractor can output a prime factor.
-/

open Round10

open scoped Classical



theorem saturator_ne_zero {S : Finset ℕ} (hS : ∀ k ∈ S, 0 < k) : saturator S ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k hk => (hS k hk).ne'

theorem dvd_saturator {S : Finset ℕ} {k : ℕ} (hk : k ∈ S) : k ∣ saturator S :=
  Finset.dvd_prod_of_mem id hk

/-- A prime `p ≡ 1 (mod ∏_{k ∈ S} k)` saturates every witness in `S`. -/
theorem gcd_eq_self_of_modEq_one {S : Finset ℕ} {p k : ℕ} (hk : k ∈ S) (hp : 1 ≤ p)
    (hmod : p ≡ 1 [MOD saturator S]) : (p - 1).gcd k = k := by
  have hdvd : saturator S ∣ p - 1 := (Nat.modEq_iff_dvd' hp).mp hmod.symm
  exact Nat.gcd_eq_right ((dvd_saturator hk).trans hdvd)

/-- **Saturating primes are abundant.**  For any finite set `S` of positive exponents and
any bound `n`, there is a prime `p > n` whose free witnesses over `S` are all maximal. -/
theorem exists_saturating_prime (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) (n : ℕ) :
    ∃ p > n, p.Prime ∧ ∀ k ∈ S, (p - 1).gcd k = k := by
  obtain ⟨p, hpn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq n (q := saturator S) (a := 1)
      (saturator_ne_zero hS) (Nat.coprime_one_left _)
  exact ⟨p, hpn, hp, fun k hk => gcd_eq_self_of_modEq_one hk hp.one_lt.le hmod⟩

/-- The joint profile of a saturating semiprime depends only on `q` and `S`. -/
theorem profile_of_saturating {S : Finset ℕ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hsat : ∀ k ∈ S, (p - 1).gcd k = k) :
    profile S (p * q) = fun k => if k ∈ S then k * (q - 1).gcd k else 0 := by
  haveI := Fact.mk hp
  haveI := Fact.mk hq
  funext k
  by_cases hk : k ∈ S
  · simp only [profile, hk, if_pos]
    rw [freeWitness_eq p q k ((Nat.coprime_primes hp hq).mpr hne), hsat k hk]
  · simp [profile, hk]


/-- **Joint-closure theorem (barrier 4).**  For every finite set `S` of positive exponents
and every prime `q`, infinitely many primes `p` give semiprimes `N = p*q` with one and the
same joint free-witness profile over `S`.

The joint of arbitrarily many partial witnesses therefore stays partial: no finite
aggregation of the family `R_k` separates the factorisations. -/
theorem joint_profile_collisions_infinite (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k)
    {q : ℕ} (hq : q.Prime) :
    {p : ℕ | p.Prime ∧ q < p ∧
        profile S (p * q) = fun k => if k ∈ S then k * (q - 1).gcd k else 0}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpa, hp, hsat⟩ := exists_saturating_prime S hS (max a q)
  have hpq : q < p := lt_of_le_of_lt (le_max_right a q) hpa
  exact ⟨p, ⟨hp, hpq, profile_of_saturating hp hq hpq.ne' hsat⟩,
    lt_of_le_of_lt (le_max_left a q) hpa⟩

/-- **Persistent collisions.**  Two distinct semiprimes sharing a prime factor `q` and
carrying literally the same joint profile over `S`. -/
theorem exists_profile_collision (S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) {q : ℕ} (hq : q.Prime) :
    ∃ p p' : ℕ, p.Prime ∧ p'.Prime ∧ q < p ∧ q < p' ∧ p ≠ p' ∧
      profile S (p * q) = profile S (p' * q) := by
  obtain ⟨p, ⟨hp, hpq, hprof⟩, p', ⟨hp', hp'q, hprof'⟩, hne⟩ :=
    (joint_profile_collisions_infinite S hS hq).nontrivial
  exact ⟨p, p', hp, hp', hpq, hp'q, hne, by rw [hprof, hprof']⟩


/-! ## Experiment 337 in concrete form

The round-10 experiment used the exponent set `{6, 12, 15, 20, 30, 60}`.  Both `61` and
`181` are primes congruent to `1` modulo `60`, so the semiprimes `61 * 7` and `181 * 7`
have identical joint profiles over that set — a persistent collision one can check by hand.
-/



open Round10 in
theorem solution(S : Finset ℕ) (hS : ∀ k ∈ S, 0 < k) {q : ℕ} (hq : q.Prime) :
    ¬ ∃ F : (ℕ → ℕ) → ℕ, ∀ p : ℕ, p.Prime → q < p → F (profile S (p * q)) = p := by
  rintro ⟨F, hF⟩
  obtain ⟨p, p', hp, hp', hpq, hp'q, hne, hprof⟩ := exists_profile_collision S hS hq
  exact hne (by rw [← hF p hp hpq, ← hF p' hp' hp'q, hprof])
