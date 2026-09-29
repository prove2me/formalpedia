-- Prove2me | solution 1 for KappaDial.cellCount_block
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:46:23.408316+00:00
-- url     : https://prove2.me/submissions/0cff9f9b-a37a-44e1-af61-69e6459fa033

-- Sol generated from Combinatorics/KappaRateDial.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaRateDial
/-
# The κ rate–dial: divisibility patterns are a rate dial, not a position dial

This file formalises, for an arbitrary finite set `P` of primes, the *divisibility cell
decomposition* of the integers and proves the two complementary statements that were
isolated empirically in the `κ`-composition layer:

* **Rate dial.** The number of integers in one full period `L = ∏_{p ∈ P} p` lying in the
  cell prescribed by a sign pattern `σ : ℕ → Bool` (`p ∣ v` exactly when `σ p = true`) is
  *exactly* the multiplicative quantity
  `κ(σ) = ∏_{p ∈ P} (if σ p then 1 else p - 1)`  (`card_period_eq_kappaRaw`).
  So the divisibility pattern rescales the *rate* by a completely factorised amount.

* **Not a position dial.** The very same count is *exactly* reproduced in every translated
  period block (`cellCount_block`), so counting over `m` periods is exactly `m · κ(σ)`
  (`cellCount_period_multiple`): the drift in the block index `t` is identically zero, and
  the ratio of two cell rates is independent of the number of periods observed
  (`cellCount_ratio_scale_invariant`) — the law is scale-carrying.

Structural consequences proved here:

* the extremal (all-cleared) cell is exactly the set of totatives, and its rate is
  `Nat.totient L` (`kappaRaw_all_false_eq_totient`, `inCell_all_false_iff_coprime`);
* `κ(σ) ≤ Nat.totient L` for every pattern, with the *sharp* equality criterion
  (`kappaRaw_eq_totient_iff`);
* `1 ≤ κ(σ)` with the dual sharp criterion (`kappaRaw_eq_one_iff`), so the full spread of
  the dial is exactly the factor `Nat.totient L` (`kappa_spread`);
* the prime `2` is a **dead coordinate** of the dial: flipping `σ` at `2` never changes the
  rate (`kappaRaw_flip_two`) — the modulation is carried by the odd primes only;
* the cells tile a period: `∑_{T ⊆ P} κ(σ_T) = L` (`sum_kappaRaw_powerset`).

## Lab notes (experimental data feeding these statements)

For `P = {2,3,5,7}`, `L = 210`:

| pattern (dividing primes) | κ | κ/(L/2^4) |
| --- | --- | --- |
| ∅ (all cleared)      | 48 | 3.657 |
| {2}                  | 48 | 3.657 |
| {7}                  |  8 | 0.610 |
| {2,3,5}              |  6 | 0.457 |
| {2,3,5,7}            |  1 | 0.076 |

The empirical observation that the *top* and *bottom* cells reproduce across independent
samples, while the positional profile stays flat to within measurement noise, is here
upgraded to an exact theorem: the positional profile is *identically* flat, and the top /
bottom cells are `∅` and `P` up to the dead `2`-coordinate.
-/


open Finset

open KappaDial

/-! ## Definitions -/






/-! ## Elementary properties of the modulus -/



/-! ## Periodicity: the cell predicate only sees `v` modulo the period -/


lemma inCell_add_mul (P : Finset ℕ) (σ : ℕ → Bool) {L : ℕ} (hL : ∀ p ∈ P, p ∣ L)
    (v m : ℕ) : InCell P σ (v + m * L) ↔ InCell P σ v := by
  unfold InCell
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have h := hL p hp
  have hd : p ∣ v + m * L ↔ p ∣ v := by
    constructor
    · intro h2
      exact (Nat.dvd_add_right (Dvd.dvd.mul_left h m)).mp (by rwa [Nat.add_comm] at h2)
    · intro h2; exact Nat.dvd_add h2 (Dvd.dvd.mul_left h m)
  rw [hd]

/-! ## The Chinese-remainder counting lemma -/



/-! ## The rate law: exact cell counts over one period -/



/-! ## The positional law: exact flatness in the block index -/





/-! ## Structure of the dial: extremes, totatives, and the dead 2-coordinate -/



  







/-! ## Closure: the cells tile a period -/



/-! ## The dichotomy theorem -/


/-! ## Worked instance: `P = {2,3,5,7}`, `L = 210` -/












open KappaDial in
theorem solution(P : Finset ℕ) (σ : ℕ → Bool) {L : ℕ} (hL : ∀ p ∈ P, p ∣ L) (m : ℕ) :
    cellCount P σ (m * L) (m * L + L) = cellCount P σ 0 L := by
  unfold cellCount
  refine Finset.card_nbij' (fun v => v - m * L) (fun v => v + m * L) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hv ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hv
    refine ⟨⟨Nat.zero_le _, by omega⟩, ?_⟩
    have e : v - m * L + m * L = v := by omega
    rw [← inCell_add_mul P σ hL (v - m * L) m, e]; exact h3
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hv ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hv
    exact ⟨⟨by omega, by omega⟩, (inCell_add_mul P σ hL v m).mpr h3⟩
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hv
    dsimp only
    omega
  · intro v hv
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hv
    dsimp only
    omega
