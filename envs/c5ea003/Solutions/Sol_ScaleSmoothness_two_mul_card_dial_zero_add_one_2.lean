-- Prove2me | solution 2 for ScaleSmoothness.two_mul_card_dial_zero_add_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T07:50:04.531178+00:00
-- url     : https://prove2.me/submissions/e843f9a1-acf6-4454-a36c-6368cde1a2ea

import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion

open ScaleSmoothness Finset

open ScaleSmoothness Finset in
/-- **An odd prime has exactly `(p-1)/2` non-residues.** -/
theorem solution (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * #{N : ZMod p | dial p N = 0} + 1 = p := by
  classical
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp
  have hdial : ∀ N : ZMod p, (dial p N : ℤ) = quadraticChar (ZMod p) N + 1 := by
    intro N
    rw [← quadraticChar_card_sqrts hF N]
    simp [dial, Set.toFinset_setOf]
  have h0 : dial p 0 = 1 := by
    have h := hdial 0
    rw [quadraticChar_zero] at h
    exact_mod_cast h
  have hnz : ∀ N : ZMod p, N ≠ 0 → dial p N = 0 ∨ dial p N = 2 := by
    intro N hN
    have h := hdial N
    rcases quadraticChar_dichotomy hN with hc | hc <;> rw [hc] at h
    · right; exact_mod_cast h
    · left; omega
  have htot : ∑ N : ZMod p, dial p N = p := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun x : ZMod p => x ^ 2)
      (s := (univ : Finset (ZMod p))) (t := univ) (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, ZMod.card] at h
    exact h.symm
  have hpt1 : ∀ N : ZMod p,
      dial p N = 2 * (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0) := by
    intro N
    by_cases hN : N = 0
    · subst hN; rw [h0]; simp
    · rcases hnz N hN with h | h <;> simp [h, hN]
  have hpt2 : ∀ N : ZMod p,
      1 = (if dial p N = 0 then 1 else 0) + (if dial p N = 2 then 1 else 0) + (if N = 0 then 1 else 0) := by
    intro N
    by_cases hN : N = 0
    · subst hN; rw [h0]; simp
    · rcases hnz N hN with h | h <;> simp [h, hN]
  have S1 : ∑ N : ZMod p, dial p N = 2 * #{N : ZMod p | dial p N = 2} + 1 := by
    rw [Finset.sum_congr rfl (fun N _ => hpt1 N), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Finset.sum_boole]
  have S2 : ∑ _N : ZMod p, (1 : ℕ)
      = #{N : ZMod p | dial p N = 0} + #{N : ZMod p | dial p N = 2} + 1 := by
    rw [Finset.sum_congr rfl (fun N _ => hpt2 N), Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp [Finset.sum_boole]
  have S3 : ∑ _N : ZMod p, (1 : ℕ) = p := by simp [ZMod.card]
  omega
