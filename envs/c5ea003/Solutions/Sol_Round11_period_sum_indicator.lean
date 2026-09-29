-- Prove2me | solution 1 for Round11.period_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:36:22.146087+00:00
-- url     : https://prove2.me/submissions/8a6558a7-ab09-494d-9855-c45b9a9ee929

-- Sol generated from Combinatorics/Round11OrbitCountSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_card_multiples_range
/-
# Round-11 Closures, Part II: the orbit-count (GROUPOID) identity, via Burnside

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypothesis **GROUPOID**).

The paper records the orbit-count ("homotopy cardinality") identity
```
C(b) = 1 + φ(N)/ord_N(b) + (p-1)/ord_p(b) + (q-1)/ord_q(b)
```
for the action of `⟨b⟩` on `ℤ/N`, `N = p·q`, and observes that it re-sums exactly
the data that factoring already requires.  Here it is *proved*, in the
division-free form
```
C(b) · n = n + (p-1)·(n/ord_p b) + (q-1)·(n/ord_q b) + (p-1)(q-1),
n = ord_N(b) = lcm (ord_p b) (ord_q b),
```
where `C(b)` is the honest number of orbits of the cyclic group `⟨b⟩ ≤ (ℤ/N)ˣ`
acting on `ℤ/N` (`Round11.groupoid_orbit_identity`).  Note `φ(N) = (p-1)(q-1)`
and the `(p-1)(q-1)` term is exactly the single free orbit `φ(N)/ord_N(b) · n`
… divided out; see `Round11.groupoid_orbit_identity_totient` for the statement
written with `Nat.totient`.

The bridge to Part I is the observation that the **cycle-index fingerprint is a
fixed-point count**:
```
#{x ∈ ℤ/N : b^k x = x} = gcd (b^k - 1) N = F(k)
```
(`Round11.card_fix_eq_fpr`), so Burnside's lemma turns the orbit count into the
average of the fingerprint over a full period.  This is the precise sense in
which the topological/groupoid re-encoding "re-sums the same sealed data": the
orbit count is a linear functional of the very fingerprint whose Möbius spectrum
Part I showed to be supported at the order scale.
-/

open Round11

open Finset MulAction

/-! ## Fixed-point counts -/



/-! ## Counting multiples -/


/-! ## The Burnside average of the fingerprint -/


/-! ## The order of `b` modulo a semiprime -/


/-! ## GROUPOID: the orbit count -/







open Round11 in
theorem solution(p q dp dq : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hdp : 0 < dp) (hdq : 0 < dq) :
    ∑ k ∈ range (Nat.lcm dp dq), (if dp ∣ k then p else 1) * (if dq ∣ k then q else 1)
      = Nat.lcm dp dq + (p - 1) * (Nat.lcm dp dq / dp) + (q - 1) * (Nat.lcm dp dq / dq)
        + (p - 1) * (q - 1) := by
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  set n := Nat.lcm dp dq with hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (fun h => by
    rw [hn, Nat.lcm_eq_zero_iff] at h; omega)
  have hdpn : dp ∣ n := Nat.dvd_lcm_left _ _
  have hdqn : dq ∣ n := Nat.dvd_lcm_right _ _
  have pointwise : ∀ k, (if dp ∣ k then p' + 1 else 1) * (if dq ∣ k then q' + 1 else 1)
      = 1 + p' * (if dp ∣ k then 1 else 0) + q' * (if dq ∣ k then 1 else 0)
        + p' * q' * (if n ∣ k then 1 else 0) := by
    intro k
    have hiff : (dp ∣ k ∧ dq ∣ k) ↔ n ∣ k := ⟨fun h => Nat.lcm_dvd h.1 h.2,
      fun h => ⟨hdpn.trans h, hdqn.trans h⟩⟩
    by_cases h1 : dp ∣ k <;> by_cases h2 : dq ∣ k <;> simp [h1, h2, hiff.symm] <;> ring
  simp only [pointwise, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one]
  rw [show (∑ k ∈ range n, if dp ∣ k then 1 else 0) = ((range n).filter (fun k => dp ∣ k)).card by
        simp [Finset.sum_boole],
      show (∑ k ∈ range n, if dq ∣ k then 1 else 0) = ((range n).filter (fun k => dq ∣ k)).card by
        simp [Finset.sum_boole],
      show (∑ k ∈ range n, if n ∣ k then 1 else 0) = ((range n).filter (fun k => n ∣ k)).card by
        simp [Finset.sum_boole],
      card_multiples_range n dp hdp hdpn, card_multiples_range n dq hdq hdqn,
      card_multiples_range n n hn0 dvd_rfl, Nat.div_self hn0]
  simp
