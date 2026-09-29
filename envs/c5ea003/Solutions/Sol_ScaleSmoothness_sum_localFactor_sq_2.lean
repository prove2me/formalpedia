-- Prove2me | solution 2 for ScaleSmoothness.sum_localFactor_sq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:04:26.534067+00:00
-- url     : https://prove2.me/submissions/7629334c-6a9d-40f7-9acf-97ae3ecbe348

import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
open ScaleSmoothness Finset in
theorem solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∑ N : ZMod p, (localFactor p N) ^ 2 = (p : ℚ) + 1 / ((p : ℚ) - 1) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp3 : 3 ≤ p := by omega
  have hne : ((p : ℚ) - 1) ≠ 0 := by
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp3
    intro h
    linarith
  -- `2` is invertible in `ZMod p` because `p` is an odd prime
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    simpa using this
  -- the dial values sum to `p` (the fibres of `x ↦ x²` partition `ZMod p`)
  have hd : ∑ N : ZMod p, dial p N = p := by
    have h : (Finset.univ : Finset (ZMod p)).card
        = ∑ N ∈ (Finset.univ : Finset (ZMod p)),
          ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = N)).card :=
      Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    simp only [dial]
    rw [← h, Finset.card_univ, ZMod.card]
  have hcast : ∑ N : ZMod p, ((dial p N : ℚ)) = (p : ℚ) := by
    rw [← Nat.cast_sum, hd]
  -- `dial p 0 = 1`: only `0` squares to `0` in a field
  have hd0 : dial p 0 = 1 := by
    show ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = 0)).card = 1
    have : ((Finset.univ : Finset (ZMod p)).filter (fun x => x ^ 2 = 0)) = {0} := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hy
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
      · intro hy
        rw [hy]
        ring
    rw [this, Finset.card_singleton]
  -- for `N ≠ 0` the fibre is either empty or the two-element set `{x, -x}`
  have hfib : ∀ N : ZMod p, N ≠ 0 → dial p N = 0 ∨ dial p N = 2 := by
    intro N hN
    by_cases hex : ∃ x : ZMod p, x ^ 2 = N
    · obtain ⟨x, hx⟩ := hex
      right
      have hx0 : x ≠ 0 := by
        intro h
        rw [h] at hx
        exact hN (by rw [← hx]; ring)
      have hxne : x ≠ -x := by
        intro h
        have h2x : (2 : ZMod p) * x = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2x with h' | h'
        · exact h2ne h'
        · exact hx0 h'
      show ((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = N)).card = 2
      have hset : ((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = N)) = {x, -x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · intro hy
          have hfac : (y - x) * (y + x) = 0 := by linear_combination hy - hx
          rcases mul_eq_zero.mp hfac with h' | h'
          · exact Or.inl (by linear_combination h')
          · exact Or.inr (by linear_combination h')
        · rintro (rfl | rfl)
          · exact hx
          · rw [← hx]; ring
      rw [hset, Finset.card_insert_of_notMem (by simpa using hxne), Finset.card_singleton]
    · left
      show ((Finset.univ : Finset (ZMod p)).filter (fun y => y ^ 2 = N)).card = 0
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y _
      exact fun h => hex ⟨y, h⟩
  -- hence `∑ dial² = 2p - 1`
  have hsplit : ∀ N : ZMod p,
      ((dial p N : ℚ)) ^ 2 = 2 * (dial p N : ℚ) - (if N = 0 then (1 : ℚ) else 0) := by
    intro N
    by_cases hN : N = 0
    · subst hN
      rw [hd0]
      norm_num
    · rcases hfib N hN with h | h <;> rw [h] <;> norm_num [hN]
  have hd2 : ∑ N : ZMod p, ((dial p N : ℚ)) ^ 2 = 2 * (p : ℚ) - 1 := by
    rw [Finset.sum_congr rfl (fun N _ => hsplit N), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hcast, Finset.sum_ite_eq' (Finset.univ : Finset (ZMod p)) (0 : ZMod p) (fun _ => (1 : ℚ))]
    simp
  -- assemble
  simp only [localFactor, div_pow]
  rw [← Finset.sum_div]
  have hnum : ∑ N : ZMod p, ((p : ℚ) - (dial p N : ℚ)) ^ 2
      = (p : ℚ) ^ 3 - 2 * (p : ℚ) ^ 2 + (2 * (p : ℚ) - 1) := by
    have hexp : ∀ N : ZMod p, ((p : ℚ) - (dial p N : ℚ)) ^ 2
        = (p : ℚ) ^ 2 - 2 * (p : ℚ) * (dial p N : ℚ) + ((dial p N : ℚ)) ^ 2 := by
      intro N; ring
    rw [Finset.sum_congr rfl (fun N _ => hexp N)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, ← Finset.mul_sum, hcast, hd2]
    ring
  rw [hnum]
  field_simp
  ring
