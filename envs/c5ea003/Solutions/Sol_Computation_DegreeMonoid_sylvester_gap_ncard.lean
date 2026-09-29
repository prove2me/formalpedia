-- Prove2me | solution 1 for Computation.DegreeMonoid.sylvester_gap_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:19:04.971792+00:00
-- url     : https://prove2.me/submissions/7e6f6f8a-55d7-4ba9-a8dc-67ac82bb4522

import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure

open Computation DegreeMonoid Finset in
theorem solution {p q : ℕ} (cop : Nat.Coprime p q) (hp : 1 < p) (hq : 1 < q) :
    {n : ℕ | n ∉ degreeMonoid (chainRel ({p, q} : Set ℕ)) 0}.ncard = (p - 1) * (q - 1) / 2 := by
  classical
  let rep : ℕ → Prop := fun n => ∃ a b : ℕ, n = a * p + b * q
  -- a positive representable number drops by `p` or by `q`
  have hstep : ∀ m, rep (m + 1) ↔ (p ≤ m + 1 ∧ rep (m + 1 - p)) ∨ (q ≤ m + 1 ∧ rep (m + 1 - q)) := by
    intro m
    constructor
    · rintro ⟨a, b, hab⟩
      rcases Nat.eq_zero_or_pos a with ha | ha
      · subst ha
        obtain ⟨b0, rfl⟩ : ∃ b0, b = b0 + 1 := by
          rcases Nat.eq_zero_or_pos b with hb | hb
          · subst hb
            simp at hab
          · exact ⟨b - 1, by omega⟩
        have h' : m + 1 = b0 * q + q := by rw [hab]; ring
        right
        exact ⟨by omega, 0, b0, by simp only [zero_mul, zero_add]; omega⟩
      · obtain ⟨a0, rfl⟩ : ∃ a0, a = a0 + 1 := ⟨a - 1, by omega⟩
        have h' : m + 1 = a0 * p + b * q + p := by rw [hab]; ring
        left
        exact ⟨by omega, a0, b, by omega⟩
    · rintro (⟨hle, a, b, hab⟩ | ⟨hle, a, b, hab⟩)
      · exact ⟨a + 1, b, by rw [add_mul, one_mul]; omega⟩
      · exact ⟨a, b + 1, by rw [add_mul b 1 q, one_mul]; omega⟩
  -- closed walks: from `j` one descends to `0`, and at `0` one runs a `p`- or `q`-cycle
  have hwalk : ∀ n j, iterR (chainRel ({p, q} : Set ℕ)) n j 0 ↔ j ≤ n ∧ rep (n - j) := by
    intro n
    induction n with
    | zero =>
      intro j
      simp only [iterR_zero]
      constructor
      · rintro rfl
        exact ⟨le_rfl, 0, 0, by simp⟩
      · rintro ⟨h, -⟩
        omega
    | succ n ih =>
      intro j
      rw [iterR_succ]
      rcases j with _ | j
      · constructor
        · rintro ⟨b, hb, hw⟩
          rw [ih] at hw
          simp only [chainRel] at hb
          rcases hb with ⟨-, hb⟩ | hb
          · rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
            refine ⟨Nat.zero_le _, ?_⟩
            rw [Nat.sub_zero, hstep n]
            rcases hb with hb | hb
            · left
              refine ⟨by omega, ?_⟩
              have e : n + 1 - p = n - b := by omega
              rw [e]
              exact hw.2
            · right
              refine ⟨by omega, ?_⟩
              have e : n + 1 - q = n - b := by omega
              rw [e]
              exact hw.2
          · omega
        · rintro ⟨-, hrep⟩
          rw [Nat.sub_zero, hstep n] at hrep
          rcases hrep with ⟨hle, hr⟩ | ⟨hle, hr⟩
          · refine ⟨p - 1, Or.inl ⟨rfl, ?_⟩, ?_⟩
            · rw [Set.mem_insert_iff]
              left
              omega
            · rw [ih]
              refine ⟨by omega, ?_⟩
              have e : n - (p - 1) = n + 1 - p := by omega
              rw [e]
              exact hr
          · refine ⟨q - 1, Or.inl ⟨rfl, ?_⟩, ?_⟩
            · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
              right
              omega
            · rw [ih]
              refine ⟨by omega, ?_⟩
              have e : n - (q - 1) = n + 1 - q := by omega
              rw [e]
              exact hr
      · constructor
        · rintro ⟨b, hb, hw⟩
          simp only [chainRel] at hb
          rcases hb with ⟨h, -⟩ | hb
          · omega
          · have hbj : b = j := by omega
            subst hbj
            rw [ih] at hw
            refine ⟨by omega, ?_⟩
            have e : n + 1 - (b + 1) = n - b := by omega
            rw [e]
            exact hw.2
        · rintro ⟨hle, hr⟩
          refine ⟨j, Or.inr rfl, ?_⟩
          rw [ih]
          refine ⟨by omega, ?_⟩
          have e : n - j = n + 1 - (j + 1) := by omega
          rw [e]
          exact hr
  have hmem : ∀ n, n ∈ degreeMonoid (chainRel ({p, q} : Set ℕ)) 0 ↔ rep n := by
    intro n
    show iterR _ n 0 0 ↔ rep n
    rw [hwalk]
    simp
  -- integer representations `n = a p + b q` with `0 ≤ a < q`
  have hcanon : ∀ n : ℕ, ∃ a : ℕ, a < q ∧ ∃ b : ℤ, (n : ℤ) = a * p + b * q := by
    intro n
    obtain ⟨a, ha, hma⟩ := Nat.exists_mul_mod_eq_of_coprime n cop (by omega)
    have hmod : p * a ≡ n [MOD q] := hma
    obtain ⟨b, hb⟩ := (Nat.modEq_iff_dvd.1 hmod)
    refine ⟨a, ha, b, ?_⟩
    push_cast at hb
    linarith
  have hrepiff : ∀ (n a : ℕ) (b : ℤ), a < q → (n : ℤ) = a * p + b * q → (rep n ↔ 0 ≤ b) := by
    intro n a b ha hn
    constructor
    · rintro ⟨a', b', h'⟩
      have h'' : (n : ℤ) = a' * p + b' * q := by exact_mod_cast h'
      have hdiv : (q : ℤ) ∣ ((a' : ℤ) - a) * p := ⟨b - b', by linear_combination hn - h''⟩
      have hcop' : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 cop.symm
      obtain ⟨t, ht⟩ := hcop'.dvd_of_dvd_mul_right hdiv
      have haq : (a : ℤ) < q := by exact_mod_cast ha
      have ha0 : (0 : ℤ) ≤ a' := by positivity
      have ht0 : 0 ≤ t := by
        by_contra hneg
        have ht1 : t ≤ -1 := by omega
        nlinarith
      have hq0 : (q : ℤ) ≠ 0 := by positivity
      have hb : b = b' + t * p := by
        apply mul_right_cancel₀ hq0
        linear_combination (h'' - hn) + (p : ℤ) * ht
      rw [hb]
      positivity
    · intro hb0
      refine ⟨a, b.toNat, ?_⟩
      have hbt : (b.toNat : ℤ) = b := Int.toNat_of_nonneg hb0
      have : (n : ℤ) = a * p + (b.toNat : ℤ) * q := by rw [hbt]; exact hn
      exact_mod_cast this
  -- the Frobenius number `c = pq - p - q`
  have hpq : p + q ≤ p * q := by nlinarith
  have hcz : ((p * q - p - q : ℕ) : ℤ) = (p : ℤ) * q - p - q := by
    rw [Nat.sub_sub, Nat.cast_sub hpq]
    push_cast
    ring
  have hc1 : p * q - p - q + 1 = (p - 1) * (q - 1) := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have e : (p' + 1) * (q' + 1) = p' * q' + p' + q' + 1 := by ring
    rw [e, Nat.add_sub_cancel, Nat.add_sub_cancel]
    omega
  -- everything above `c` is representable
  have hbig : ∀ n, p * q - p - q < n → rep n := by
    intro n hn
    obtain ⟨a, ha, b, hab⟩ := hcanon n
    refine (hrepiff n a b ha hab).2 ?_
    by_contra hneg
    have hb1 : b ≤ -1 := by omega
    have hn' : ((p * q - p - q : ℕ) : ℤ) + 1 ≤ n := by exact_mod_cast hn
    rw [hcz] at hn'
    have ha' : (a : ℤ) ≤ q - 1 := by
      have : (a : ℤ) < q := by exact_mod_cast ha
      linarith
    have hp0 : (0 : ℤ) ≤ p := by positivity
    have hq0 : (0 : ℤ) ≤ q := by positivity
    nlinarith [mul_le_mul_of_nonneg_right ha' hp0, mul_le_mul_of_nonneg_right hb1 hq0]
  -- `n ↦ c - n` swaps representable and non-representable numbers in `[0, c]`
  have hsym : ∀ n, n ≤ p * q - p - q → (rep n ↔ ¬ rep (p * q - p - q - n)) := by
    intro n hn
    obtain ⟨a, ha, b, hab⟩ := hcanon n
    have h1 := hrepiff n a b ha hab
    have h2 := hrepiff (p * q - p - q - n) (q - 1 - a) (-1 - b) (by omega) (by
      rw [Nat.cast_sub hn, Nat.cast_sub (by omega : a ≤ q - 1), hcz,
        Nat.cast_sub (by omega : 1 ≤ q)]
      push_cast
      linear_combination (-1 : ℤ) * hab)
    rw [h1, h2]
    omega
  have hset : {n : ℕ | n ∉ degreeMonoid (chainRel ({p, q} : Set ℕ)) 0}
      = ↑((Finset.range (p * q - p - q + 1)).filter (fun n => ¬ rep n)) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.coe_filter, Finset.mem_range, hmem]
    constructor
    · intro h
      exact ⟨by by_contra hc'; exact h (hbig n (by omega)), h⟩
    · rintro ⟨-, h⟩
      exact h
  rw [hset, Set.ncard_coe_finset]
  have hswap : ((Finset.range (p * q - p - q + 1)).filter (fun n => ¬ rep n)).card
      = ((Finset.range (p * q - p - q + 1)).filter rep).card := by
    exact Finset.card_bij' (fun n _ => p * q - p - q - n) (fun n _ => p * q - p - q - n)
      (fun n hn => by
        simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
        refine ⟨by omega, ?_⟩
        by_contra hr
        exact hn.2 ((hsym n (by omega)).2 hr))
      (fun n hn => by
        simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
        exact ⟨by omega, (hsym n (by omega)).1 hn.2⟩)
      (fun n hn => by
        rw [Finset.mem_filter, Finset.mem_range] at hn
        show p * q - p - q - (p * q - p - q - n) = n
        omega)
      (fun n hn => by
        rw [Finset.mem_filter, Finset.mem_range] at hn
        show p * q - p - q - (p * q - p - q - n) = n
        omega)
  have htot := Finset.card_filter_add_card_filter_not
    (s := Finset.range (p * q - p - q + 1)) rep
  rw [Finset.card_range] at htot
  omega
