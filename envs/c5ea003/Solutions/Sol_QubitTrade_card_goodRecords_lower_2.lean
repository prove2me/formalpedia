-- Prove2me | solution 2 for QubitTrade.card_goodRecords_lower
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:21:01.2587+00:00
-- url     : https://prove2.me/submissions/ffe68b62-61ba-4538-a661-319aa21797af

import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SuccessDensity
open QubitTrade Finset in
theorem solution {r m : ℕ} (hr : 0 < r) (hm : 2 ≤ m) :
    (2 ^ (m - 1) - 1) * r ^ m < 2 ^ (m - 1) * (goodRecords r m).card := by
  -- the bad records are fewer than `r^m / 2^(m-1)`
  have hbad : 2 ^ (m - 1) * (badRecords r m).card < r ^ m := by
    classical
    -- `Σ_{p ∈ S} 1/p² < 1/2` for every finite set of primes
    have hprime : ∀ (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p) →
        ∑ p ∈ S, (1:ℚ) / (p : ℚ) ^ 2 < 1 / 2 := by
      intro S hS
      -- telescoping: `Σ_{2 ≤ k < M} (1/k − 1/(k+1)) = 1/2 − 1/M`
      have htel : ∀ M : ℕ, 2 ≤ M → ∑ k ∈ Ico 2 M, ((1:ℚ) / k - 1 / (k + 1)) = 1 / 2 - 1 / M := by
        intro M hM
        induction M, hM using Nat.le_induction with
        | base => simp
        | succ M hM ih =>
          rw [sum_Ico_succ_top hM, ih]
          have : (M : ℚ) ≠ 0 := by positivity
          push_cast
          field_simp
          ring
      rw [← sum_filter_add_sum_filter_not S (fun p => p < 5)]
      -- the primes below `5` are `2` and `3`
      have hsmall : ∑ p ∈ S.filter (fun p => p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ 1 / 4 + 1 / 9 := by
        have hsub : S.filter (fun p => p < 5) ⊆ {2, 3} := by
          intro p hp
          rw [mem_filter] at hp
          have hpr := hS p hp.1
          have h2 := hpr.two_le
          have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by norm_num)
          simp only [mem_insert, mem_singleton]
          omega
        calc _ ≤ ∑ p ∈ ({2, 3} : Finset ℕ), (1:ℚ) / (p : ℚ) ^ 2 :=
              sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
          _ = 1 / 4 + 1 / 9 := by norm_num
      -- a prime `p ≥ 5` is `2k+1` with `k ≥ 2`, and `1/(2k+1)² ≤ (1/k − 1/(k+1))/4`
      set g : ℕ → ℚ := fun k => ((1:ℚ) / k - 1 / (k + 1)) / 4 with hg
      have hodd : ∀ p ∈ S.filter (fun p => ¬ p < 5), p % 2 = 1 ∧ 5 ≤ p := by
        intro p hp
        rw [mem_filter] at hp
        have hpr := hS p hp.1
        exact ⟨Nat.odd_iff.mp (hpr.odd_of_ne_two (by omega)), by omega⟩
      have hgpos : ∀ k : ℕ, 1 ≤ k → 0 ≤ g k := by
        intro k hk
        have hk' : (1 : ℚ) ≤ k := by exact_mod_cast hk
        simp only [hg]
        rw [div_sub_div _ _ (by positivity) (by positivity)]
        apply div_nonneg (div_nonneg (by linarith) (by positivity)) (by norm_num)
      have hterm : ∀ p ∈ S.filter (fun p => ¬ p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ g ((p - 1) / 2) := by
        intro p hp
        obtain ⟨h1, h5⟩ := hodd p hp
        obtain ⟨k, rfl⟩ : ∃ k, p = 2 * k + 1 := ⟨p / 2, by omega⟩
        have hk : (2 * k + 1 - 1) / 2 = k := by omega
        rw [hk]
        have hk2 : (2 : ℚ) ≤ k := by exact_mod_cast (by omega : 2 ≤ k)
        have hgk : g k = 1 / (4 * (k : ℚ) * (k + 1)) := by
          simp only [hg]
          field_simp
          ring
        rw [hgk]
        push_cast
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      -- sum over the large primes via the injective map `p ↦ (p−1)/2` into `[2, M)`
      set M := S.sup id + 2 with hM
      have hlarge : ∑ p ∈ S.filter (fun p => ¬ p < 5), (1:ℚ) / (p : ℚ) ^ 2 ≤ 1 / 8 := by
        calc _ ≤ ∑ p ∈ S.filter (fun p => ¬ p < 5), g ((p - 1) / 2) := sum_le_sum hterm
          _ = ∑ k ∈ (S.filter (fun p => ¬ p < 5)).image (fun p => (p - 1) / 2), g k := by
              rw [sum_image]
              intro p hp q hq hpq
              have := hodd p hp
              have := hodd q hq
              simp only at hpq
              omega
          _ ≤ ∑ k ∈ Ico 2 M, g k := by
              apply sum_le_sum_of_subset_of_nonneg
              · intro k hk
                obtain ⟨p, hp, rfl⟩ := mem_image.mp hk
                have := hodd p hp
                have hle : p ≤ S.sup id := le_sup (f := id) (mem_filter.mp hp).1
                rw [mem_Ico]
                omega
              · intro k hk _
                exact hgpos k (by rw [mem_Ico] at hk; omega)
          _ = (1 / 2 - 1 / M) / 4 := by
              rw [hg, ← sum_div, htel M (by omega)]
          _ ≤ 1 / 8 := by
              have : (0 : ℚ) ≤ 1 / M := by positivity
              linarith
      linarith
    -- the record gcd divides every entry
    have hdvdG : ∀ (l : List ℕ), ∀ x ∈ l, recordGcd l ∣ x := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih =>
        intro x hx
        simp only [recordGcd, List.foldr_cons] at ih ⊢
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.gcd_dvd_left _ _
        · exact (Nat.gcd_dvd_right _ _).trans (ih x hx)
    -- a bad record has all entries divisible by some prime factor of `r`
    have hsub : badRecords r m ⊆ r.primeFactors.biUnion (fun p => multipleRecords r m p) := by
      intro f hf
      simp only [badRecords, allRecords, mem_filter, Fintype.mem_piFinset, mem_range] at hf
      obtain ⟨hlt, hg⟩ := hf
      have hp : (Nat.gcd (recordGcd (List.ofFn f)) r).minFac.Prime := Nat.minFac_prime hg
      have hpg := Nat.minFac_dvd (Nat.gcd (recordGcd (List.ofFn f)) r)
      rw [mem_biUnion]
      refine ⟨_, Nat.mem_primeFactors.mpr ⟨hp, hpg.trans (Nat.gcd_dvd_right _ _), hr.ne'⟩, ?_⟩
      simp only [multipleRecords, Fintype.mem_piFinset, mem_filter, mem_range]
      intro i
      refine ⟨hlt i, (hpg.trans (Nat.gcd_dvd_left _ _)).trans (hdvdG _ (f i) ?_)⟩
      exact (List.mem_ofFn' f (f i)).mpr ⟨i, rfl⟩
    -- there are exactly `(r/p)^m` records of multiples of `p`
    have hmul : ∀ p ∈ r.primeFactors, (multipleRecords r m p).card = (r / p) ^ m := by
      intro p hp
      have hpp := Nat.mem_primeFactors.mp hp
      obtain ⟨s, hs⟩ := hpp.2.1
      have hpos := hpp.1.pos
      have hcnt : ((range r).filter (fun x => p ∣ x)).card = r / p := by
        have : (range r).filter (fun x => p ∣ x) = (range s).image (fun j => p * j) := by
          ext x
          simp only [mem_filter, mem_range, mem_image]
          constructor
          · rintro ⟨hx, t, rfl⟩
            rw [hs] at hx
            exact ⟨t, (Nat.mul_lt_mul_left hpos).mp hx, rfl⟩
          · rintro ⟨t, ht, rfl⟩
            rw [hs]
            exact ⟨(Nat.mul_lt_mul_left hpos).mpr ht, dvd_mul_right _ _⟩
        rw [this, card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hpos h),
          card_range, hs, Nat.mul_div_cancel_left _ hpos]
      simp only [multipleRecords, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
        hcnt]
    -- union bound
    have hcard : ((badRecords r m).card : ℚ) ≤ ∑ p ∈ r.primeFactors, ((r : ℚ) / p) ^ m := by
      have h1 := (card_le_card hsub).trans card_biUnion_le
      rw [sum_congr rfl hmul] at h1
      have h2 : ((badRecords r m).card : ℚ) ≤ ∑ p ∈ r.primeFactors, ((r / p : ℕ) : ℚ) ^ m := by
        exact_mod_cast h1
      refine h2.trans (le_of_eq (sum_congr rfl (fun p hp => ?_)))
      have hpp := Nat.mem_primeFactors.mp hp
      rw [Nat.cast_div hpp.2.1 (by exact_mod_cast hpp.1.ne_zero)]
    -- `(r/p)^m ≤ r^m / 2^(m-2) · 1/p²`
    have hterm : ∀ p ∈ r.primeFactors,
        ((r : ℚ) / p) ^ m ≤ (r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * (1 / (p : ℚ) ^ 2) := by
      intro p hp
      have hp2 : (2 : ℚ) ≤ p := by exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
      have hpm : (p : ℚ) ^ m = p ^ 2 * p ^ (m - 2) := by
        rw [← pow_add]
        congr 1
        omega
      have hK : (2 : ℚ) ^ (m - 2) ≤ (p : ℚ) ^ (m - 2) := pow_le_pow_left₀ (by norm_num) hp2 _
      rw [div_pow, hpm, div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have hr' : (0 : ℚ) ≤ (r : ℚ) ^ m := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hK (by positivity : (0 : ℚ) ≤ (p : ℚ) ^ 2)]
    have hsum : ∑ p ∈ r.primeFactors, ((r : ℚ) / p) ^ m < (r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * (1 / 2) := by
      calc _ ≤ ∑ p ∈ r.primeFactors, (r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * (1 / (p : ℚ) ^ 2) :=
            sum_le_sum hterm
        _ = (r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * ∑ p ∈ r.primeFactors, 1 / (p : ℚ) ^ 2 := by
            rw [mul_sum]
        _ < (r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * (1 / 2) :=
            mul_lt_mul_of_pos_left (hprime _ (fun p hp => (Nat.mem_primeFactors.mp hp).1))
              (by positivity)
    have hfin : (2 : ℚ) ^ (m - 1) * (badRecords r m).card < (r : ℚ) ^ m := by
      have h2 : (2 : ℚ) ^ (m - 1) = 2 * (2 : ℚ) ^ (m - 2) := by
        rw [← pow_succ']
        congr 1
        omega
      have hK0 : (2 : ℚ) ^ (m - 2) ≠ 0 := by positivity
      calc (2 : ℚ) ^ (m - 1) * (badRecords r m).card
          ≤ (2 : ℚ) ^ (m - 1) * ∑ p ∈ r.primeFactors, ((r : ℚ) / p) ^ m :=
            mul_le_mul_of_nonneg_left hcard (by positivity)
        _ < (2 : ℚ) ^ (m - 1) * ((r : ℚ) ^ m / (2 : ℚ) ^ (m - 2) * (1 / 2)) :=
            mul_lt_mul_of_pos_left hsum (by positivity)
        _ = (r : ℚ) ^ m := by
            rw [h2]
            field_simp
    exact_mod_cast hfin
  -- good and bad records partition all `r^m` records
  have htot : (goodRecords r m).card + (badRecords r m).card = r ^ m := by
    unfold goodRecords badRecords
    rw [card_filter_add_card_filter_not]
    simp [allRecords, Fintype.card_piFinset]
  have hA : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have e1 : (2 ^ (m - 1) - 1) * r ^ m = 2 ^ (m - 1) * r ^ m - r ^ m := by
    rw [Nat.sub_one_mul]
  have e2 : 2 ^ (m - 1) * r ^ m
      = 2 ^ (m - 1) * (goodRecords r m).card + 2 ^ (m - 1) * (badRecords r m).card := by
    rw [← htot, mul_add]
  have hb1 : (badRecords r m).card ≤ 2 ^ (m - 1) * (badRecords r m).card :=
    Nat.le_mul_of_pos_left _ (by positivity)
  have hg1 : (goodRecords r m).card ≤ 2 ^ (m - 1) * (goodRecords r m).card :=
    Nat.le_mul_of_pos_left _ (by positivity)
  rw [e1, e2]
  omega
