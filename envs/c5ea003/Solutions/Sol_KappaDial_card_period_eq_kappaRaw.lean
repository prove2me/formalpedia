-- Prove2me | solution 1 for KappaDial.card_period_eq_kappaRaw
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:44:57.648166+00:00
-- url     : https://prove2.me/submissions/9b90deb5-3fca-4c5a-83de-7cfae88675d1

-- Sol generated from Combinatorics/KappaRateDial.lean
import Mathlib
import Definitions.Def_Combinatorics_KappaRateDial
import Theorems.Thm_KappaDial_card_range_dvd_cell
import Theorems.Thm_KappaDial_count_mul_coprime
import Theorems.Thm_KappaDial_inCell_periodic
import Theorems.Thm_KappaDial_modulus_pos
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
theorem solution(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (σ : ℕ → Bool) :
    ((range (modulus P)).filter (InCell P σ)).card = kappaRaw P σ := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      have h : (range (modulus (∅ : Finset ℕ))).filter (InCell ∅ σ) = {0} := by
        simp only [modulus, Finset.prod_empty]
        rw [Finset.filter_true_of_mem (fun x _ => by intro p hp; simp at hp)]
        rfl
      rw [h]; simp [kappaRaw]
  | insert q P' hq ih =>
      have hqp : q.Prime := hP q (Finset.mem_insert_self q P')
      have hP' : ∀ p ∈ P', p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hmod : modulus (insert q P') = q * modulus P' := by
        simp [modulus, Finset.prod_insert hq]
      have hcop : Nat.Coprime q (modulus P') :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes hqp (hP' p hp)).mpr (fun h => hq (h ▸ hp))
      have hL'pos : 0 < modulus P' := modulus_pos P' hP'
      have hfilter : ∀ v, InCell (insert q P') σ v ↔ ((q ∣ v ↔ σ q = true) ∧ InCell P' σ v) := by
        intro v; unfold InCell; simp
      rw [hmod, Finset.filter_congr (fun v _ => (hfilter v)),
        count_mul_coprime q (modulus P') hqp.pos hL'pos hcop _ _
          (fun v w hvw => by
            have hd : q ∣ v ↔ q ∣ w := by
              rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hvw]
            rw [hd])
          (fun v w hvw =>
            inCell_periodic P' σ (fun p hp => Finset.dvd_prod_of_mem _ hp) v w hvw),
        card_range_dvd_cell q hqp.pos (σ q), ih hP']
      simp [kappaRaw, Finset.prod_insert hq]
