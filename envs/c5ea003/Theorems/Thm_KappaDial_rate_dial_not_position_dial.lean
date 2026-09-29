-- Prove2me | Theorems.Thm_KappaDial_rate_dial_not_position_dial
-- name    : KappaDial.rate_dial_not_position_dial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:20:00.671341+00:00
-- url     : https://prove2.me/theorems/9904f0cf-ae8f-4e56-a61e-25a99963537f
-- title:
--   Divisibility is a rate dial, not a position dial.
-- statement:
--   **Divisibility is a rate dial, not a position dial.**
--
--   For any finite set `P` of primes with period `L`:
--   1. *(no positional signal)* every period block, at every offset `m`, contains exactly the
--      same number of cell members, and counting over `m` periods is exactly `m · κ(σ)` —
--      the positional profile is identically flat with zero drift;
--   2. *(a genuine rate signal)* as soon as `P` contains an odd prime, the rate `κ` really does
--      vary between cells, by the full factor `Nat.totient L ≥ 2`.
--
--   ```lean
--   theorem KappaDial.rate_dial_not_position_dial(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
--       (hodd : ∃ p ∈ P, p ≠ 2) :
--       (∀ (σ : ℕ → Bool) (m : ℕ),
--           cellCount P σ (m * modulus P) (m * modulus P + modulus P) = cellCount P σ 0 (modulus P)) ∧
--       (∀ (σ : ℕ → Bool) (m : ℕ), cellCount P σ 0 (m * modulus P) = m * kappaRaw P σ) ∧
--       (2 ≤ Nat.totient (modulus P) ∧
--         kappaRaw P (fun _ => false) = Nat.totient (modulus P) * kappaRaw P (fun _ => true)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/KappaRateDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/KappaRateDial.lean#L451

-- Thm stub generated from Combinatorics/KappaRateDial.lean
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

theorem KappaDial.rate_dial_not_position_dial(P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hodd : ∃ p ∈ P, p ≠ 2) :
    (∀ (σ : ℕ → Bool) (m : ℕ),
        cellCount P σ (m * modulus P) (m * modulus P + modulus P) = cellCount P σ 0 (modulus P)) ∧
    (∀ (σ : ℕ → Bool) (m : ℕ), cellCount P σ 0 (m * modulus P) = m * kappaRaw P σ) ∧
    (2 ≤ Nat.totient (modulus P) ∧
      kappaRaw P (fun _ => false) = Nat.totient (modulus P) * kappaRaw P (fun _ => true)) := by sorry
