-- Prove2me | solution 1 for EllipticModCount.two_dvd_cardPoints_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:14:36.742073+00:00
-- url     : https://prove2.me/submissions/4480bee2-1eda-4a3f-9728-1cdba5146998

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
open EllipticModCount Finset in
theorem solution {F : Type*} [Field F] [Fintype F] [DecidableEq F] {a b : F}
    (hF : ringChar F ≠ 2) (hd : disc a b ≠ 0) :
    2 ∣ cardPoints a b ↔ ∃ x : F, x ^ 3 + a * x + b = 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  -- two distinct roots force exactly three
  have htwo : ∀ r s : F, wRHS a b r = 0 → wRHS a b s = 0 → r ≠ s → (rootSet a b).card = 3 := by
    intro r s hr hs hrs
    have H : rootSet a b = {r, s, -(r + s)} ∧ (rootSet a b).card = 3 := by
        unfold wRHS at hr hs
        -- Vieta: `a = -(r² + rs + s²)`, `b = rs(r + s)`
        have hrs' : r - s ≠ 0 := sub_ne_zero.mpr hrs
        have ha : a = -(r ^ 2 + r * s + s ^ 2) := by
          have : (r - s) * (r ^ 2 + r * s + s ^ 2 + a) = (r - s) * 0 := by
            linear_combination hr - hs
          have := mul_left_cancel₀ hrs' this
          linear_combination this
        have hb : b = r * s * (r + s) := by
          rw [ha] at hr
          linear_combination hr
        have hfac : ∀ x, wRHS a b x = (x - r) * (x - s) * (x + (r + s)) := by
          intro x
          unfold wRHS
          rw [ha, hb]
          ring
        -- the discriminant is `-(r - s)²(2r + s)²(r + 2s)²`
        have hdisc : disc a b = -((r - s) * (2 * r + s) * (r + 2 * s)) ^ 2 := by
          unfold disc
          rw [ha, hb]
          ring
        have hprod : (r - s) * (2 * r + s) * (r + 2 * s) ≠ 0 := by
          intro h0
          apply hd
          rw [hdisc, h0]
          ring
        have h1 : 2 * r + s ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
        have h2 : r + 2 * s ≠ 0 := fun h0 => hprod (by rw [h0]; ring)
        have hrt : r ≠ -(r + s) := fun h0 => h1 (by linear_combination h0)
        have hst : s ≠ -(r + s) := fun h0 => h2 (by linear_combination h0)
        have hset : rootSet a b = {r, s, -(r + s)} := by
          ext x
          simp only [rootSet, mem_filter, mem_univ, true_and, hfac, mem_insert, mem_singleton,
            mul_eq_zero, sub_eq_zero]
          constructor
          · rintro ((h | h) | h)
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (by linear_combination h))
          · rintro (h | h | h)
            · exact Or.inl (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (by rw [h]; ring)
        refine ⟨hset, ?_⟩
        rw [hset]
        exact card_eq_three.mpr ⟨r, s, -(r + s), hrs, hrt, hst, rfl⟩
    exact H.2

  -- so the number of roots is `0`, `1` or `3`
  have hroots : (rootSet a b).card = 0 ∨ (rootSet a b).card = 1 ∨ (rootSet a b).card = 3 := by
    rcases (rootSet a b).eq_empty_or_nonempty with h0 | ⟨r, hr⟩
    · left
      rw [h0, card_empty]
    · by_cases hex : ∃ s ∈ rootSet a b, s ≠ r
      · obtain ⟨s, hs, hsr⟩ := hex
        right; right
        exact htwo r s (mem_filter.mp hr).2 (mem_filter.mp hs).2 (Ne.symm hsr)
      · right; left
        push_neg at hex
        rw [card_eq_one]
        exact ⟨r, eq_singleton_iff_unique_mem.mpr ⟨hr, hex⟩⟩
  -- a finite set closed under a fixed-point-free negation has even size
  have hpar : ∀ (n : ℕ) (S : Finset F), S.card = n → (∀ y ∈ S, -y ∈ S) →
      (∀ y ∈ S, -y ≠ y) → Even n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hcl hne
      rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · rw [← hS]
        simp
      · have hmem : -v ∈ S.erase v := mem_erase.mpr ⟨hne v hv, hcl v hv⟩
        have h2c : 1 < S.card := one_lt_card.mpr ⟨v, hv, -v, hcl v hv, (hne v hv).symm⟩
        have hcard : ((S.erase v).erase (-v)).card = n - 2 := by
          rw [card_erase_of_mem hmem, card_erase_of_mem hv, hS]
          omega
        have hcl' : ∀ y ∈ (S.erase v).erase (-v), -y ∈ (S.erase v).erase (-v) := by
          intro y hy
          simp only [mem_erase] at hy ⊢
          refine ⟨fun h => hy.2.1 ?_, fun h => hy.1 ?_, hcl y hy.2.2⟩
          · rw [← neg_neg y, h, neg_neg]
          · rw [← neg_neg y, h]
        have hne' : ∀ y ∈ (S.erase v).erase (-v), -y ≠ y := fun y hy =>
          hne y (mem_of_mem_erase (mem_of_mem_erase hy))
        obtain ⟨k, hk⟩ := ih (n - 2) (by omega) _ hcard hcl' hne'
        exact ⟨k + 1, by omega⟩
  -- the fibre `{y | y² = c}` has odd size iff `c = 0`
  have hfib : ∀ c : F, (univ.filter (fun y : F => y ^ 2 = c)).card % 2 = if c = 0 then 1 else 0 := by
    intro c
    split_ifs with hc
    · subst hc
      have : univ.filter (fun y : F => y ^ 2 = 0) = {0} := by
        ext y
        simp [pow_eq_zero_iff]
      rw [this, card_singleton]
    · obtain ⟨k, hk⟩ := hpar _ (univ.filter (fun y : F => y ^ 2 = c)) rfl
        (fun y hy => by simp only [mem_filter, mem_univ, true_and] at hy ⊢; rw [neg_sq]; exact hy)
        (fun y hy h => by
          simp only [mem_filter, mem_univ, true_and] at hy
          have hy0 : y = 0 := by
            have : (2 : F) * y = 0 := by linear_combination -h
            exact (mul_eq_zero.mp this).resolve_left h2
          rw [hy0] at hy
          exact hc (by rw [← hy]; ring))
      omega
  -- count affine points fibrewise over `x`
  have haff : (affineLocus a b).card = ∑ x : F, (univ.filter (fun y : F => y ^ 2 = wRHS a b x)).card := by
    unfold affineLocus
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl (fun x _ => ?_)
    rw [card_filter]
  have hmod : (affineLocus a b).card % 2 = (rootSet a b).card % 2 := by
    rw [haff, sum_nat_mod]
    simp only [hfib]
    unfold rootSet
    rw [card_filter]
  have hex : (∃ x : F, x ^ 3 + a * x + b = 0) ↔ (rootSet a b).card ≠ 0 := by
    rw [Ne, card_eq_zero]
    constructor
    · rintro ⟨x, hx⟩ h0
      have hmem : x ∈ rootSet a b := mem_filter.mpr ⟨mem_univ _, hx⟩
      rw [h0] at hmem
      simp at hmem
    · intro h0
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h0
      exact ⟨x, (mem_filter.mp hx).2⟩
  rw [hex]
  unfold cardPoints
  rw [Nat.dvd_iff_mod_eq_zero]
  rcases hroots with h | h | h <;> rw [h] at hmod ⊢ <;> omega
