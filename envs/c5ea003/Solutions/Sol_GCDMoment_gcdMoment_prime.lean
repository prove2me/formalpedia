-- Prove2me | solution 1 for GCDMoment.gcdMoment_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:56:24.917791+00:00
-- url     : https://prove2.me/submissions/e07bb6e3-b340-4f06-84d1-7d541927dfd0

/-
# `GCDMoment.gcdMoment_prime`
Target `51ab1cef` (Open; re-read live before submitting).

ORDINARY PROOF — bundles recovered from the graph, Theorems screen CLEAN. Gift: SAFE.

BINDERS — this target has NO WA, and its home bundle Def_Novelty_GCDMomentMultiplicative has NO
`variable` lines at all, so the published statement's binders are complete:
    ∀ {p : ℕ}, p.Prime → ∀ (k : ℕ), gcdMoment k p = p ^ k + p - 1

DEFINITION (read from source, TraceWitness:61):
    gcdMoment k n = ∑ x ∈ Finset.range n, (n.gcd x) ^ k

MATHS. Split range p at x = 0: that term is gcd(p,0)^k = p^k. Every other x has 0 < x < p, so a
prime p cannot divide it and gcd(p,x) = 1, contributing 1 each over p-1 terms. Total p^k + (p-1).

PROBED, NOT GUESSED — all five names #checked in a probe that compiled:
  * `Finset.card_range : #(range n) = n`   (my first guess `Nat.card_range` does NOT exist)
  * `Finset.sum_range_succ' f n : ∑ k ∈ range (n+1), f k = ∑ k ∈ range n, f (k+1) + f 0`
  * `Nat.not_dvd_of_pos_of_lt : 0 < n → n < m → ¬m ∣ n`
-/
import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative

set_option autoImplicit false
set_option maxHeartbeats 400000

open GCDMoment Finset

open GCDMoment in
/-- **The target, verbatim.** -/
theorem solution {p : ℕ} (hp : p.Prime) (k : ℕ) : gcdMoment k p = p ^ k + p - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  rw [gcdMoment, Finset.sum_range_succ']
  have hg : ∀ i ∈ Finset.range m, Nat.gcd (m + 1) (i + 1) ^ k = 1 := by
    intro i hi
    have hlt : i + 1 < m + 1 := by have := Finset.mem_range.mp hi; omega
    rw [(Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos i) hlt), one_pow]
  rw [Finset.sum_congr rfl hg]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Nat.gcd_zero_right]
  omega
