-- Prove2me | solution 1 for QubitTrade.card_goodRecords_eq_euler_product
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T00:02:08.448232+00:00
-- url     : https://prove2.me/submissions/69494c16-9c99-4e8a-b353-e22edc797a7d

import Mathlib
import Definitions.Def_Algebra_QubitTrade_JordanCount
import Definitions.Def_Algebra_QubitTrade_SuccessDensity

set_option maxHeartbeats 3200000 in
open Finset QubitTrade in
theorem solution {r m : ℕ} (hr : 0 < r) :
    ((goodRecords r m).card : ℚ)
      = (r : ℚ) ^ m * ∏ p ∈ r.primeFactors, (1 - ((p : ℚ) ^ m)⁻¹) := by
  classical
  -- the two record lemmas, proved from their definitions
  have recordGcd_dvd_mem : ∀ {k : ℕ} {ks : List ℕ}, k ∈ ks → recordGcd ks ∣ k := by
    have hrec : ∀ (a : ℕ) (as : List ℕ), recordGcd (a :: as) = Nat.gcd a (recordGcd as) :=
      fun _ _ => rfl
    intro k ks
    induction ks with
    | nil => intro h; exact absurd h (List.not_mem_nil)
    | cons a as ih =>
        intro h
        rw [hrec]
        rcases List.mem_cons.mp h with rfl | h'
        · exact Nat.gcd_dvd_left _ _
        · exact dvd_trans (Nat.gcd_dvd_right _ _) (ih h')
  have card_multipleRecords : ∀ {r m p : ℕ}, 0 < p → p ∣ r →
      (multipleRecords r m p).card = (r / p) ^ m := by
    intro r m p hp hd
    obtain ⟨t, rfl⟩ := hd
    have hdiv : p * t / p = t := Nat.mul_div_cancel_left t hp
    have hinj : Function.Injective (fun x : ℕ => p * x) :=
      fun a b h => Nat.eq_of_mul_eq_mul_left hp h
    have hset : (Finset.range (p * t)).filter (fun x => p ∣ x)
        = (Finset.range t).image (fun x => p * x) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hx, c, rfl⟩
        exact ⟨c, lt_of_mul_lt_mul_left hx (Nat.zero_le p), rfl⟩
      · rintro ⟨c, hc, rfl⟩
        exact ⟨(Nat.mul_lt_mul_left hp).mpr hc, c, rfl⟩
    unfold multipleRecords
    rw [Fintype.card_piFinset]
    rw [hdiv]
    simp [hset, Finset.card_image_of_injective _ hinj]
  -- a number divides the record gcd exactly when it divides every entry
  have hgcd_all : ∀ (d : ℕ) (L : List ℕ), (∀ x ∈ L, d ∣ x) → d ∣ recordGcd L := by
    intro d L
    induction L with
    | nil => intro _; simp [recordGcd]
    | cons a t ih =>
      intro h
      have ha : d ∣ a := h a (List.mem_cons_self ..)
      have ht : d ∣ recordGcd t := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      simpa [recordGcd] using Nat.dvd_gcd ha ht
  have hdvd_iff : ∀ (d : ℕ) (f : Fin m → ℕ),
      d ∣ recordGcd (List.ofFn f) ↔ ∀ i, d ∣ f i := by
    intro d f
    constructor
    · intro h i
      exact dvd_trans h (recordGcd_dvd_mem (List.mem_ofFn.mpr ⟨i, rfl⟩))
    · intro h
      refine hgcd_all d _ ?_
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact h i
  -- goodness says no prime factor of `r` divides every entry
  have hfilter_eq : goodRecords r m
      = (allRecords r m).filter (fun f => ∀ p ∈ r.primeFactors, ¬ (∀ i, p ∣ f i)) := by
    rw [goodRecords]
    refine Finset.filter_congr ?_
    intro f _
    constructor
    · intro hg p hp hdiv
      have hpd : p ∣ recordGcd (List.ofFn f) := (hdvd_iff p f).mpr hdiv
      have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp
      have h1 : p ∣ Nat.gcd (recordGcd (List.ofFn f)) r := Nat.dvd_gcd hpd hpr
      rw [hg] at h1
      exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp h1)
    · intro hne
      by_contra hg
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
      have hpr : p ∣ r := hpd.trans (Nat.gcd_dvd_right _ _)
      have hpg : p ∣ recordGcd (List.ofFn f) := hpd.trans (Nat.gcd_dvd_left _ _)
      exact hne p (Nat.mem_primeFactors.mpr ⟨hp, hpr, by omega⟩) ((hdvd_iff p f).mp hpg)
  -- a set of primes divides every entry exactly when their product does
  have hprod_iff : ∀ (t : Finset ℕ), t ⊆ r.primeFactors → ∀ f : Fin m → ℕ,
      (∀ p ∈ t, ∀ i, p ∣ f i) ↔ (∀ i, (∏ p ∈ t, p) ∣ f i) := by
    intro t ht f
    constructor
    · intro h i
      refine Finset.prod_primes_dvd _ ?_ ?_
      · intro p hp
        exact (Nat.prime_of_mem_primeFactors (ht hp)).prime
      · intro p hp
        exact h p hp i
    · intro h p hp i
      exact dvd_trans (Finset.dvd_prod_of_mem _ hp) (h i)
  -- expand the goodness indicator over subsets of the prime factors
  have hind : ∀ f : Fin m → ℕ,
      (if (∀ p ∈ r.primeFactors, ¬ (∀ i, p ∣ f i)) then (1:ℚ) else 0)
        = ∑ t ∈ r.primeFactors.powerset,
            (-1:ℚ)^t.card * (if (∀ i, (∏ p ∈ t, p) ∣ f i) then (1:ℚ) else 0) := by
    intro f
    have hexp : ∀ g : ℕ → ℚ,
        ∏ p ∈ r.primeFactors, (1 + g p) = ∑ t ∈ r.primeFactors.powerset, ∏ p ∈ t, g p := by
      intro g
      simpa [add_comm] using Finset.prod_add g (fun _ => (1:ℚ)) r.primeFactors
    have h1 : ∏ p ∈ r.primeFactors,
        (1 + (-(if (∀ i, p ∣ f i) then (1:ℚ) else 0)))
          = if (∀ p ∈ r.primeFactors, ¬ (∀ i, p ∣ f i)) then (1:ℚ) else 0 := by
      by_cases hgood : ∀ p ∈ r.primeFactors, ¬ (∀ i, p ∣ f i)
      · rw [if_pos hgood]
        refine Finset.prod_eq_one ?_
        intro p hp
        rw [if_neg (hgood p hp)]
        ring
      · rw [if_neg hgood]
        push_neg at hgood
        obtain ⟨p, hp, hdiv⟩ := hgood
        refine Finset.prod_eq_zero hp ?_
        rw [if_pos hdiv]
        ring
    rw [← h1, hexp]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.mem_powerset] at ht
    have h2 : ∏ p ∈ t, (-(if (∀ i, p ∣ f i) then (1:ℚ) else 0))
        = (-1:ℚ)^t.card * ∏ p ∈ t, (if (∀ i, p ∣ f i) then (1:ℚ) else 0) := by
      rw [Finset.prod_neg]
    rw [h2]
    congr 1
    by_cases hall : ∀ p ∈ t, ∀ i, p ∣ f i
    · rw [if_pos ((hprod_iff t ht f).mp hall)]
      refine Finset.prod_eq_one ?_
      intro p hp
      rw [if_pos (hall p hp)]
    · rw [if_neg (fun hc => hall ((hprod_iff t ht f).mpr hc))]
      push_neg at hall
      obtain ⟨p, hp, hnd⟩ := hall
      refine Finset.prod_eq_zero hp ?_
      rw [if_neg (not_forall.mpr hnd)]
  -- membership in the record finsets
  have hallmem : ∀ f : Fin m → ℕ, f ∈ allRecords r m ↔ ∀ i, f i ∈ Finset.range r := by
    intro f
    simp [allRecords, Fintype.mem_piFinset]
  have hmulmem : ∀ (D : ℕ) (f : Fin m → ℕ),
      f ∈ multipleRecords r m D ↔ (∀ i, f i ∈ Finset.range r) ∧ (∀ i, D ∣ f i) := by
    intro D f
    simp only [multipleRecords, Fintype.mem_piFinset, Finset.mem_filter]
    constructor
    · intro h; exact ⟨fun i => (h i).1, fun i => (h i).2⟩
    · intro h i; exact ⟨h.1 i, h.2 i⟩
  -- the count as an alternating sum over subsets of the prime factors
  have hcount : ((goodRecords r m).card : ℚ)
      = ∑ t ∈ r.primeFactors.powerset,
          (-1:ℚ)^t.card * ((multipleRecords r m (∏ p ∈ t, p)).card : ℚ) := by
    rw [hfilter_eq, Finset.card_filter]
    push_cast
    rw [Finset.sum_congr rfl (fun f _ => hind f), Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [← Finset.mul_sum]
    congr 1
    have hset : (allRecords r m).filter (fun f => ∀ i, (∏ p ∈ t, p) ∣ f i)
        = multipleRecords r m (∏ p ∈ t, p) := by
      ext f
      rw [Finset.mem_filter, hmulmem, hallmem]
    rw [← hset, Finset.card_filter]
    push_cast
    rfl
  -- the Euler product expands the same way
  have hRHS : (r : ℚ) ^ m * ∏ p ∈ r.primeFactors, (1 - ((p : ℚ) ^ m)⁻¹)
      = ∑ t ∈ r.primeFactors.powerset,
          (-1:ℚ)^t.card * ((r:ℚ) / (∏ p ∈ t, (p:ℚ)))^m := by
    have hfun : (fun p : ℕ => (1:ℚ) - ((p:ℚ)^m)⁻¹)
        = (fun p : ℕ => 1 + (-(((p:ℚ)^m)⁻¹))) := by
      funext p; ring
    have hexp2 : ∏ p ∈ r.primeFactors, ((1:ℚ) + (-(((p:ℚ)^m)⁻¹)))
        = ∑ t ∈ r.primeFactors.powerset, ∏ p ∈ t, (-(((p:ℚ)^m)⁻¹)) := by
      simpa [add_comm] using
        Finset.prod_add (fun p : ℕ => (-(((p:ℚ)^m)⁻¹))) (fun _ => (1:ℚ)) r.primeFactors
    rw [hfun, hexp2, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro t ht
    rw [Finset.mem_powerset] at ht
    rw [Finset.prod_neg]
    have hinv : ∏ p ∈ t, (((p:ℚ)^m)⁻¹) = ((∏ p ∈ t, (p:ℚ))^m)⁻¹ := by
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    rw [hinv, div_pow]
    ring
  rw [hcount, hRHS]
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [Finset.mem_powerset] at ht
  congr 1
  have hdvd : (∏ p ∈ t, p) ∣ r :=
    Finset.prod_primes_dvd r
      (fun p hp => (Nat.prime_of_mem_primeFactors (ht hp)).prime)
      (fun p hp => Nat.dvd_of_mem_primeFactors (ht hp))
  have hpos : 0 < ∏ p ∈ t, p :=
    Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors (ht hp)).pos)
  have hposQ : ((∏ p ∈ t, p : ℕ) : ℚ) ≠ 0 := by
    have : (∏ p ∈ t, p) ≠ 0 := by omega
    exact_mod_cast this
  rw [card_multipleRecords hpos hdvd]
  push_cast [Nat.cast_div hdvd hposQ]
  rfl
