-- Prove2me | solution 1 for KappaDial.rate_dial_not_position_dial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:30.480218+00:00
-- url     : https://prove2.me/submissions/f8182776-a191-43c2-b618-7f6b3885f8cf

-- Sol generated from Combinatorics/KappaRateDial.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaRateDial
import Theorems.Thm_KappaDial_cellCount_block
import Theorems.Thm_KappaDial_cellCount_period_multiple
import Theorems.Thm_KappaDial_dvd_modulus
import Theorems.Thm_KappaDial_kappaRaw_all_false_eq_totient
import Theorems.Thm_KappaDial_kappaRaw_eq_one_iff
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

lemma one_le_kappa_term {p : ℕ} (hp : p.Prime) (b : Bool) : 1 ≤ (if b then 1 else p - 1) := by
  have := hp.two_le
  cases b with
  | true => simp
  | false => simp only [Bool.false_eq_true, if_false]; omega


  


/-- Every cell is nonempty per period: the rate is at least one. -/
theorem one_le_kappaRaw (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (σ : ℕ → Bool) :
    1 ≤ kappaRaw P σ := by
  rw [kappaRaw]
  exact Finset.one_le_prod' fun p hp => one_le_kappa_term (hP p hp) (σ p)





/-! ## Closure: the cells tile a period -/



/-! ## The dichotomy theorem -/


/-! ## Worked instance: `P = {2,3,5,7}`, `L = 210` -/












open KappaDial in
theorem solution(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hodd : ∃ p ∈ P, p ≠ 2) :
    (∀ (σ : ℕ → Bool) (m : ℕ),
        cellCount P σ (m * modulus P) (m * modulus P + modulus P) = cellCount P σ 0 (modulus P)) ∧
    (∀ (σ : ℕ → Bool) (m : ℕ), cellCount P σ 0 (m * modulus P) = m * kappaRaw P σ) ∧
    (2 ≤ Nat.totient (modulus P) ∧
      kappaRaw P (fun _ => false) = Nat.totient (modulus P) * kappaRaw P (fun _ => true)) := by
  refine ⟨fun σ m => cellCount_block P σ (fun p hp => dvd_modulus P hp) m,
    fun σ m => cellCount_period_multiple P hP σ m, ?_, ?_⟩
  · obtain ⟨p, hp, hp2⟩ := hodd
    have hp3 : 3 ≤ p := by
      have := (hP p hp).two_le
      rcases Nat.lt_or_ge p 3 with h | h
      · omega
      · exact h
    have hdvd : (p - 1) ∣ kappaRaw P (fun _ => false) := by
      have := Finset.dvd_prod_of_mem (fun p => if (false : Bool) then 1 else p - 1) hp
      simpa [kappaRaw] using this
    have hpos : 0 < kappaRaw P (fun _ => false) := one_le_kappaRaw P hP _
    have : p - 1 ≤ kappaRaw P (fun _ => false) := Nat.le_of_dvd hpos hdvd
    rw [kappaRaw_all_false_eq_totient P hP] at this
    omega
  · rw [(kappaRaw_eq_one_iff P hP (fun _ => true)).mpr (fun p _ _ => rfl),
      kappaRaw_all_false_eq_totient P hP, mul_one]
