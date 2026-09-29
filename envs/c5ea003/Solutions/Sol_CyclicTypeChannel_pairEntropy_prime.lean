-- Prove2me | solution 1 for CyclicTypeChannel.pairEntropy_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T00:16:11.115249+00:00
-- url     : https://prove2.me/submissions/469c833e-937f-4b8a-a36b-845e97a748ce

import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelPrime
open CyclicTypeChannel Finset in
theorem solution {p : ℕ} (hp : p.Prime) :
    pairEntropy p = 2 * Real.logb 2 p - 2 * ((p : ℝ) - 1) / (p : ℝ) ^ 2
      - 2 * ((p : ℝ) - 1) * Real.logb 2 ((p : ℝ) - 1) / (p : ℝ) := by
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
  unfold pairEntropy
  exact hH
