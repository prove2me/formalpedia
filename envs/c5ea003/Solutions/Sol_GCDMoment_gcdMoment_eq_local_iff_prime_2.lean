-- Prove2me | solution 2 for GCDMoment.gcdMoment_eq_local_iff_prime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:53:29.694259+00:00
-- url     : https://prove2.me/submissions/fdf3f361-562a-4a7f-8bf4-53f26faec4f3

/-
# `GCDMoment.gcdMoment_eq_local_iff_prime`
Target `e44735c7`. Open, GIFT: **SAFE** (its only submission is a SKETCH on the target itself, and
proving the conclusion outright beats the sketch). Taking this voids the exposure that has
`51ab1cef gcdMoment_prime` parked.

BINDERS: no WA exists. Its home bundle `Def_Novelty_GCDMomentMultiplicative` has NO `variable` lines,
so the published statement's own binders are complete — the same situation as `gcdMoment_prime`,
which reading settled correctly.

MATHS. `gcdMoment k n = ∑_{x < n} gcd(n,x)^k`. Split `range n` by coprimality:
  * coprime x  ⇒ gcd = 1, contributing `1` each, and there are exactly `φ n` of them
                 (`Nat.totient_eq_card_coprime`, which is `rfl`);
  * x = 0      ⇒ gcd n 0 = n, contributing `n^k`;
  * the rest   ⇒ gcd ≥ 2 and k ≥ 1, so each term is ≥ 2, and there are `n - φ n - 1` of them.
So the sum is `n^k + φ n + T` with `T ≥ 2·(n - φ n - 1)`. Since `n ≥ 2`, the target value is
`n^k + (n-1)`, so equality holds iff `φ n + T = n - 1`. If `φ n = n - 1` the erased set is EMPTY so
`T = 0` and equality holds; if `φ n < n - 1`, put `d = n - 1 - φ n > 0` and then
`φ n + T ≥ φ n + 2d = (n-1-d) + 2d = n-1+d > n-1`. `Nat.totient_eq_iff_prime` converts
`φ n = n - 1` into `n.Prime`.
-/
import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative

set_option maxHeartbeats 800000

open GCDMoment Finset

open GCDMoment in
/-- **The target, verbatim.** -/
theorem solution {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    gcdMoment k n = n ^ k + n - 1 ↔ n.Prime := by
  have hn0 : 0 < n := by omega
  set C : Finset ℕ := (Finset.range n).filter (fun x => Nat.Coprime n x) with hC
  set D : Finset ℕ := (Finset.range n).filter (fun x => ¬ Nat.Coprime n x) with hD
  -- the coprime block contributes exactly φ n
  have hCcard : C.card = n.totient := by
    rw [hC, Nat.totient_eq_card_coprime]
  have hsplit : gcdMoment k n
      = (∑ x ∈ C, (Nat.gcd n x) ^ k) + ∑ x ∈ D, (Nat.gcd n x) ^ k := by
    rw [gcdMoment, hC, hD]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hCsum : (∑ x ∈ C, (Nat.gcd n x) ^ k) = n.totient := by
    have : ∀ x ∈ C, (Nat.gcd n x) ^ k = 1 := by
      intro x hx
      have hco := (Finset.mem_filter.mp (hC ▸ hx)).2
      rw [Nat.Coprime] at hco
      rw [hco, one_pow]
    rw [Finset.sum_congr rfl this, Finset.sum_const, hCcard, smul_eq_mul, mul_one]
  -- 0 sits in the non-coprime block and contributes n ^ k
  have h0D : (0 : ℕ) ∈ D := by
    rw [hD, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hn0, ?_⟩
    rw [Nat.Coprime, Nat.gcd_zero_right]
    omega
  have hDsum : (∑ x ∈ D, (Nat.gcd n x) ^ k)
      = n ^ k + ∑ x ∈ D.erase 0, (Nat.gcd n x) ^ k := by
    rw [← Finset.add_sum_erase _ _ h0D, Nat.gcd_zero_right]
  -- every surviving term is at least 2
  have hterm : ∀ x ∈ D.erase 0, 2 ≤ (Nat.gcd n x) ^ k := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have hxD := (Finset.mem_erase.mp hx).2
    have hnc := (Finset.mem_filter.mp (hD ▸ hxD)).2
    have h2 : 2 ≤ Nat.gcd n x := by
      rcases Nat.lt_or_ge (Nat.gcd n x) 2 with hlt | hge
      · interval_cases hg : Nat.gcd n x
        · exact absurd (Nat.eq_zero_of_gcd_eq_zero_left hg) (by omega)
        · exact absurd hg hnc
      · exact hge
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
      _ ≤ (Nat.gcd n x) ^ k := Nat.pow_le_pow_left h2 k
  have hTge : 2 * (D.erase 0).card ≤ ∑ x ∈ D.erase 0, (Nat.gcd n x) ^ k := by
    calc 2 * (D.erase 0).card = ∑ _x ∈ D.erase 0, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ D.erase 0, (Nat.gcd n x) ^ k := Finset.sum_le_sum hterm
  -- cardinalities
  have hCD : C.card + D.card = n := by
    rw [hC, hD, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_range]
  have hphi : n.totient ≤ n - 1 := by
    have := Nat.totient_lt n (by omega)
    omega
  have hDcard : D.card = n - n.totient := by omega
  have hEcard : (D.erase 0).card = n - n.totient - 1 := by
    rw [Finset.card_erase_of_mem h0D, hDcard]
  constructor
  · -- equality forces φ n = n - 1, hence primality
    intro heq
    rw [← Nat.totient_eq_iff_prime hn0]
    by_contra hne
    have hlt : n.totient < n - 1 := lt_of_le_of_ne hphi hne
    have hbig : n ^ k + (n - 1) < gcdMoment k n := by
      rw [hsplit, hCsum, hDsum]
      have := hTge
      rw [hEcard] at this
      omega
    omega
  · -- primality makes the erased block empty
    intro hp
    have hteq : n.totient = n - 1 := (Nat.totient_eq_iff_prime hn0).mpr hp
    have hE : (D.erase 0).card = 0 := by rw [hEcard, hteq]; omega
    have hEempty : D.erase 0 = ∅ := Finset.card_eq_zero.mp hE
    rw [hsplit, hCsum, hDsum, hEempty, Finset.sum_empty, hteq]
    omega
