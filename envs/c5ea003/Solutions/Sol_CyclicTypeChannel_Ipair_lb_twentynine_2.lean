-- Prove2me | solution 2 for CyclicTypeChannel.Ipair_lb_twentynine
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:10:40.375895+00:00
-- url     : https://prove2.me/submissions/45b56d16-594c-4304-904c-d9d517ddc8b8

import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
open CyclicTypeChannel Finset in
theorem solution : (15619 / 1722368 : ℝ) ≤ Ipair 29 := by
  -- the closed form of the type-pair channel at a prime order
  have hgen : ∀ {p : ℕ}, p.Prime → Ipair p = Real.logb 2 p
        - ((p : ℝ) - 1) * (2 * (p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) ^ 2
        + ((p : ℝ) - 1) * ((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) / (p : ℝ) ^ 2 := by
    intro p hp
    have hp1 : 1 < p := hp.one_lt
    have hp0 : 0 < p := hp.pos
    -- the splitting type: `1` at the zero exponent, `p` elsewhere
    have hord : ∀ a < p, ordType p a = if a = 0 then 1 else p := by
      intro a ha
      unfold ordType
      split_ifs with h0
      · rw [h0, Nat.gcd_zero_left, Nat.div_self hp0]
      · have : Nat.gcd a p = 1 :=
          (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
            (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h0) ha)))
        rw [this, Nat.div_one]
    -- the number of zero exponents
    obtain ⟨z, hz⟩ : ∃ z : ℕ × ℕ → ℕ,
        ∀ x, z x = (if x.1 = 0 then 1 else 0) + (if x.2 = 0 then 1 else 0) := ⟨_, fun _ => rfl⟩
    have hz3 : ∀ x, z x ∈ range 3 := by
      intro x; rw [hz, mem_range]; split_ifs <;> omega
    -- on the CyclicTypeChannel.box, the type pair is determined by (and determines) the zero count
    have htz : ∀ x ∈ CyclicTypeChannel.box p, ∀ y ∈ CyclicTypeChannel.box p, typePair p x = typePair p y ↔ z x = z y := by
      intro x hx y hy
      simp only [CyclicTypeChannel.box, mem_product, mem_range] at hx hy
      simp only [typePair, hord _ hx.1, hord _ hx.2, hord _ hy.1, hord _ hy.2, hz, Prod.mk.injEq]
      split_ifs <;> simp <;> omega
    -- entropy sums only see the zero-count classes
    have hsum : ∀ s : Finset (ℕ × ℕ), s ⊆ CyclicTypeChannel.box p →
        ∑ a ∈ s, Real.logb 2 (#{x ∈ s | typePair p x = typePair p a} : ℝ)
          = ∑ v ∈ range 3, (#{x ∈ s | z x = v} : ℝ) * Real.logb 2 (#{x ∈ s | z x = v} : ℝ) := by
      intro s hs
      have h1 : ∀ a ∈ s, #{x ∈ s | typePair p x = typePair p a} = #{x ∈ s | z x = z a} := by
        intro a ha
        rw [filter_congr (fun x hx => htz x (hs hx) a (hs ha))]
      rw [sum_congr rfl (fun a ha => by rw [h1 a ha])]
      rw [← sum_fiberwise_of_maps_to (g := z) (t := range 3) (fun a _ => hz3 a)]
      refine sum_congr rfl (fun v _ => ?_)
      rw [sum_congr rfl (g := fun _ => Real.logb 2 (#{x ∈ s | z x = v} : ℝ))
        (fun a ha => by rw [(mem_filter.mp ha).2]), sum_const, nsmul_eq_mul]
    have htot : ∀ s : Finset (ℕ × ℕ), (s.card : ℝ) = ∑ v ∈ range 3, (#{x ∈ s | z x = v} : ℝ) := by
      intro s
      rw [card_eq_sum_card_fiberwise (f := z) (t := range 3) (fun a _ => hz3 a)]
      push_cast
      rfl
    -- residues of sums of exponents
    have hm1 : ∀ m, m < 2 * p → m % p = if m < p then m else m - p := by
      intro m hm
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hFeq : ∀ c, ({x ∈ CyclicTypeChannel.box p | prodRes p x = c} : Finset (ℕ × ℕ))
        = {x ∈ CyclicTypeChannel.box p | (if x.1 + x.2 < p then x.1 + x.2 else x.1 + x.2 - p) = c} := by
      intro c
      refine filter_congr (fun x hx => ?_)
      simp only [CyclicTypeChannel.box, mem_product, mem_range] at hx
      rw [prodRes, hm1 _ (by omega)]
    -- counts on the CyclicTypeChannel.box
    have hboxc : ((CyclicTypeChannel.box p).card : ℝ) = (p : ℝ) ^ 2 := by
      rw [CyclicTypeChannel.box, card_product, card_range]; push_cast; ring
    have hb2 : #{x ∈ CyclicTypeChannel.box p | z x = 2} = 1 := by
      rw [card_eq_one]
      refine ⟨(0, 0), ?_⟩
      ext ⟨a, b⟩
      simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, mem_singleton, Prod.mk.injEq]
      split_ifs <;> omega
    have hb0 : #{x ∈ CyclicTypeChannel.box p | z x = 0} = (p - 1) * (p - 1) := by
      have : ({x ∈ CyclicTypeChannel.box p | z x = 0} : Finset (ℕ × ℕ)) = ((range p).erase 0) ×ˢ ((range p).erase 0) := by
        ext ⟨a, b⟩
        simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, mem_erase]
        by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
          simp only [ha, hb, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true,
            true_and, and_true, false_and, and_false] <;> (try simp)
      rw [this, card_product, card_erase_of_mem (mem_range.mpr hp0), card_range]
    have hb1 : (#{x ∈ CyclicTypeChannel.box p | z x = 1} : ℝ) = 2 * ((p : ℝ) - 1) := by
      have h := htot (CyclicTypeChannel.box p)
      rw [hboxc, sum_range_succ, sum_range_succ, sum_range_one, hb2, hb0] at h
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)] at h
      linarith
    -- fibres of the residue map
    have hFc : ∀ c < p, (#{x ∈ CyclicTypeChannel.box p | prodRes p x = c} : ℝ) = p := by
      intro c hc
      have : ({x ∈ CyclicTypeChannel.box p | prodRes p x = c} : Finset (ℕ × ℕ))
          = (range p).image (fun a => (a, if a ≤ c then c - a else c + p - a)) := by
        rw [hFeq]
        ext ⟨a, b⟩
        simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, mem_image, Prod.mk.injEq]
        constructor
        · rintro ⟨⟨ha, hb⟩, h⟩
          refine ⟨a, ha, rfl, ?_⟩
          split_ifs at h ⊢ <;> omega
        · rintro ⟨a', ha', rfl, rfl⟩
          refine ⟨⟨ha', ?_⟩, ?_⟩ <;> split_ifs <;> omega
      rw [this, card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), card_range]
    have hF0_2 : #{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = 0} | z x = 2} = 1 := by
      rw [card_eq_one]
      refine ⟨(0, 0), ?_⟩
      rw [hFeq]
      ext ⟨a, b⟩
      simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, mem_singleton, Prod.mk.injEq]
      split_ifs <;> omega
    have hF0_1 : #{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = 0} | z x = 1} = 0 := by
      rw [card_eq_zero, hFeq]
      ext ⟨a, b⟩
      simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, Finset.notMem_empty, iff_false]
      split_ifs <;> omega
    have hFc_2 : ∀ c, 0 < c → c < p → #{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = c} | z x = 2} = 0 := by
      intro c hc0 hc
      rw [card_eq_zero, hFeq]
      ext ⟨a, b⟩
      simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, Finset.notMem_empty, iff_false]
      split_ifs <;> omega
    have hFc_1 : ∀ c, 0 < c → c < p → #{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = c} | z x = 1} = 2 := by
      intro c hc0 hc
      have : ({x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = c} | z x = 1} : Finset (ℕ × ℕ)) = {(0, c), (c, 0)} := by
        rw [hFeq]
        ext ⟨a, b⟩
        simp only [mem_filter, CyclicTypeChannel.box, mem_product, mem_range, hz, mem_insert, mem_singleton,
          Prod.mk.injEq]
        split_ifs <;> omega
      rw [this, card_pair (by simp only [ne_eq, Prod.mk.injEq]; omega)]
    -- real-valued shorthands
    have hP0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hP1 : (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < p := by exact_mod_cast hp1
      linarith
    have hL2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    -- the pair entropy
    have hH : uEnt (CyclicTypeChannel.box p) (typePair p)
        = 2 * Real.logb 2 p - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
          - 2 * ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) := by
      unfold uEnt
      rw [hsum _ subset_rfl, sum_range_succ, sum_range_succ, sum_range_one, hb2, hb0, hb1, hboxc]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      rw [Real.logb_pow, Real.logb_mul hP1 hP1, Real.logb_mul (by norm_num) hP1, hL2, Real.logb_one]
      field_simp
      ring
    -- the two kinds of residue fibre
    have hU0 : uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = 0} (typePair p)
        = Real.logb 2 p - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / p := by
      have hn : (#{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = 0} | z x = 0} : ℝ) = p - 1 := by
        have h := htot {x ∈ CyclicTypeChannel.box p | prodRes p x = 0}
        rw [hFc 0 hp0, sum_range_succ, sum_range_succ, sum_range_one, hF0_1, hF0_2] at h
        push_cast at h
        linarith
      unfold uEnt
      rw [hsum _ (filter_subset _ _), sum_range_succ, sum_range_succ, sum_range_one, hF0_1, hF0_2,
        hn, hFc 0 hp0]
      simp only [Nat.cast_zero, Nat.cast_one, zero_mul, Real.logb_one, mul_zero, add_zero]
    have hUc : ∀ c, 0 < c → c < p → uEnt {x ∈ CyclicTypeChannel.box p | prodRes p x = c} (typePair p)
        = Real.logb 2 p - (((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) + 2) / p := by
      intro c hc0 hc
      have hn : (#{x ∈ {x ∈ CyclicTypeChannel.box p | prodRes p x = c} | z x = 0} : ℝ) = p - 2 := by
        have h := htot {x ∈ CyclicTypeChannel.box p | prodRes p x = c}
        rw [hFc c hc, sum_range_succ, sum_range_succ, sum_range_one, hFc_1 c hc0 hc,
          hFc_2 c hc0 hc] at h
        push_cast at h
        linarith
      unfold uEnt
      rw [hsum _ (filter_subset _ _), sum_range_succ, sum_range_succ, sum_range_one,
        hFc_1 c hc0 hc, hFc_2 c hc0 hc, hn, hFc c hc]
      push_cast
      rw [hL2]
      simp only [zero_mul, add_zero, Real.logb_zero, mul_zero]
      ring
    -- the residue map hits every class
    have himage : (CyclicTypeChannel.box p).image (prodRes p) = range p := by
      ext c
      simp only [mem_image, mem_range, CyclicTypeChannel.box, mem_product, prodRes, Prod.exists]
      constructor
      · rintro ⟨a, b, -, rfl⟩
        exact Nat.mod_lt _ hp0
      · intro hc
        exact ⟨c, 0, ⟨hc, hp0⟩, by rw [add_zero, Nat.mod_eq_of_lt hc]⟩
    have hC : condEnt (CyclicTypeChannel.box p) (typePair p) (prodRes p)
        = (p : ℝ) / (p : ℝ) ^ 2 * (Real.logb 2 p - ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / p)
          + ((p : ℝ) - 1) * ((p : ℝ) / (p : ℝ) ^ 2 *
            (Real.logb 2 p - (((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) + 2) / p)) := by
      unfold condEnt
      rw [himage, ← add_sum_erase _ _ (mem_range.mpr hp0), hFc 0 hp0, hU0, hboxc]
      congr 1
      rw [sum_congr rfl (g := fun _ => (p : ℝ) / (p : ℝ) ^ 2 *
            (Real.logb 2 p - (((p : ℝ) - 2) * Real.logb 2 ((p : ℝ) - 2) + 2) / p)) (fun c hc => by
          have hc' := mem_erase.mp hc
          rw [mem_range] at hc'
          rw [hFc c hc'.2, hUc c (Nat.pos_of_ne_zero hc'.1) hc'.2])]
      rw [sum_const, card_erase_of_mem (mem_range.mpr hp0), card_range, nsmul_eq_mul]
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      ring
    unfold Ipair mutInfo
    rw [hH, hC]
    field_simp
    ring
  have hp : Nat.Prime 29 := by norm_num
  rw [hgen hp]
  -- `2^23 · 28^(3·1596) ≤ 29^(3·841) · 27^(3·756)`, checked by the kernel
  have hN : 2 ^ 23 * 28 ^ (3 * 1596) ≤ 29 ^ (3 * 841) * 27 ^ (3 * 756) := by decide +kernel
  have hR : (2 : ℝ) ^ 23 * (28 : ℝ) ^ (3 * 1596) ≤ (29 : ℝ) ^ (3 * 841) * (27 : ℝ) ^ (3 * 756) := by
    exact_mod_cast hN
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hR
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)] at hlog
  rw [show ((29 : ℕ) : ℝ) = 29 by norm_num, show (29 : ℝ) - 1 = 28 by norm_num,
    show (29 : ℝ) - 2 = 27 by norm_num]
  push_cast at hlog
  linarith
