-- Prove2me | solution 1 for KappaDial.count_mul_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:43:26.519286+00:00
-- url     : https://prove2.me/submissions/33ca95ec-64d2-4250-84cc-4ec0d1ee6a7c

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



/-! ## The Chinese-remainder counting lemma -/



/-! ## The rate law: exact cell counts over one period -/



/-! ## The positional law: exact flatness in the block index -/





/-! ## Structure of the dial: extremes, totatives, and the dead 2-coordinate -/



  







/-! ## Closure: the cells tile a period -/



/-! ## The dichotomy theorem -/


/-! ## Worked instance: `P = {2,3,5,7}`, `L = 210` -/












open KappaDial in
theorem solution(q L : ℕ) (hq : 0 < q) (hL : 0 < L) (h : Nat.Coprime q L)
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B]
    (hA : ∀ v w, v % q = w % q → (A v ↔ A w))
    (hB : ∀ v w, v % L = w % L → (B v ↔ B w)) :
    ((range (q * L)).filter (fun v => A v ∧ B v)).card
      = ((range q).filter A).card * ((range L).filter B).card := by
  rw [← Finset.card_product]
  refine Finset.card_nbij (fun v => (v % q, v % L)) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, Finset.mem_product] at hv ⊢
    obtain ⟨_, hA', hB'⟩ := hv
    exact ⟨⟨Nat.mod_lt _ hq, (hA (v % q) v (Nat.mod_mod_of_dvd _ dvd_rfl)).mpr hA'⟩,
      ⟨Nat.mod_lt _ hL, (hB (v % L) v (Nat.mod_mod_of_dvd _ dvd_rfl)).mpr hB'⟩⟩
  · intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hv hw
    simp only [Prod.mk.injEq] at hvw
    have hmod : v ≡ w [MOD q * L] :=
      (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hvw.1, hvw.2⟩
    have h1 := Nat.mod_eq_of_lt hv.1
    have h2 := Nat.mod_eq_of_lt hw.1
    unfold Nat.ModEq at hmod
    omega
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨⟨hx1, hA'⟩, ⟨hx2, hB'⟩⟩ := hx
    obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder h x.1 x.2
    have e1 : k % (q * L) % q = x.1 := by
      rw [Nat.mod_mod_of_dvd k ⟨L, rfl⟩, hk1, Nat.mod_eq_of_lt hx1]
    have e2 : k % (q * L) % L = x.2 := by
      rw [Nat.mod_mod_of_dvd k ⟨q, by ring⟩, hk2, Nat.mod_eq_of_lt hx2]
    refine ⟨k % (q * L), ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (by positivity), ?_, ?_⟩
      · exact (hA _ x.1 (by rw [e1, Nat.mod_eq_of_lt hx1])).mpr hA'
      · exact (hB _ x.2 (by rw [e2, Nat.mod_eq_of_lt hx2])).mpr hB'
    · simp [e1, e2]
