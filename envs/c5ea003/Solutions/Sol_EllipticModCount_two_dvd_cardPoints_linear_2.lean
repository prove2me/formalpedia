-- Prove2me | solution 2 for EllipticModCount.two_dvd_cardPoints_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:59:34.225405+00:00
-- url     : https://prove2.me/submissions/a2e85078-542f-417c-9296-ed503dd3f365

import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticVerticalMoment
open EllipticModCount Finset in
theorem solution {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    2 ∣ cardPoints a (0 : ZMod p) := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  -- a nonzero value has an even number of square roots (`y ↦ -y` pairs them up)
  have hsq : ∀ c : ZMod p, c ≠ 0 → Even (univ.filter fun y : ZMod p => y ^ 2 = c).card := by
    intro c hc
    by_cases hr : ∃ r : ZMod p, r ^ 2 = c
    · obtain ⟨r, hr⟩ := hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        exact hc (by rw [← hr]; ring)
      have hne : r ≠ -r := by
        intro h
        apply hr0
        have : 2 * r = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_left h2
      have hset : (univ.filter fun y : ZMod p => y ^ 2 = c) = {r, -r} := by
        ext y
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        rw [← hr, sq_eq_sq_iff_eq_or_eq_neg]
      rw [hset, card_pair hne]
      exact even_two
    · push Not at hr
      have hset : (univ.filter fun y : ZMod p => y ^ 2 = c) = ∅ := by
        ext y
        simp [hr y]
      rw [hset, card_empty]
      exact ⟨0, rfl⟩
  -- count the affine points fibre by fibre over `x`
  have hfib : (affineLocus a (0 : ZMod p)).card
      = ∑ x : ZMod p, (univ.filter fun y : ZMod p => y ^ 2 = wRHS a 0 x).card := by
    unfold affineLocus
    rw [card_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun x _ => ?_
    rw [card_filter]
  -- split the fibres by whether the right-hand side vanishes
  set Z := univ.filter fun x : ZMod p => wRHS a 0 x = 0 with hZ
  have hsplit := sum_filter_add_sum_filter_not univ (fun x : ZMod p => wRHS a 0 x = 0)
    (fun x => (univ.filter fun y : ZMod p => y ^ 2 = wRHS a 0 x).card)
  have hzero : ∑ x ∈ Z, (univ.filter fun y : ZMod p => y ^ 2 = wRHS a 0 x).card = Z.card := by
    rw [card_eq_sum_ones]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_filter] at hx
    rw [hx.2]
    have : (univ.filter fun y : ZMod p => y ^ 2 = 0) = {0} := by
      ext y
      simp
    rw [this, card_singleton]
  have heven : Even (∑ x ∈ univ.filter (fun x : ZMod p => ¬ wRHS a 0 x = 0),
      (univ.filter fun y : ZMod p => y ^ 2 = wRHS a 0 x).card) :=
    Finset.even_sum _ fun x hx => hsq _ (mem_filter.mp hx).2
  -- the roots of `x³ + a x = x (x² + a)`: `0`, and an even number of roots of `x² = -a`
  have hZodd : Odd Z.card := by
    have hZeq : Z = insert 0 (univ.filter fun x : ZMod p => x ^ 2 = -a) := by
      ext x
      simp only [hZ, mem_filter, mem_univ, true_and, mem_insert, wRHS]
      constructor
      · intro h
        have : x * (x ^ 2 + a) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (by linear_combination h0)
      · rintro (h0 | h0)
        · rw [h0]; ring
        · linear_combination x * h0
    have h0 : (0 : ZMod p) ∉ univ.filter fun x : ZMod p => x ^ 2 = -a := by
      simp only [mem_filter, mem_univ, true_and]
      intro h
      apply ha
      linear_combination h
    rw [hZeq, card_insert_of_notMem h0]
    exact (hsq (-a) (neg_ne_zero.mpr ha)).add_one
  unfold cardPoints
  rw [hfib, ← hsplit, hzero]
  exact (hZodd.add_even heven).add_one.two_dvd
