-- Prove2me | solution 1 for ScaleSmoothness.dial_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:42:00.020107+00:00
-- url     : https://prove2.me/submissions/7d3faef3-366b-4aa7-844a-048f6ade44d8

-- Sol generated from NumberTheory/QRDialLocalStatistics.lean
import Mathlib
import Definitions.Def_NumberTheory_QRDialLocalStatistics
import Theorems.Thm_ScaleSmoothness_dial_eq_zero_of_not_isSquare

/-!
# The quadratic-residue dial of `x² − N`: exact local statistics

This file is the rigorous local half of the round-73 #4 (exp 562) finding
**SCALE-SMOOTHNESS-DEVIATION / RANDOM-AT-SCALE**: numerically the `B`-smoothness
probability of the quadratic-sieve polynomial `x² − N` was found to be
indistinguishable from that of size-matched random integers
(`r(u) = 1.011, 0.949, 0.900, 1.200` at `u ≈ 5.96, 6.95, 7.93, 8.26`, all
confidence intervals covering `1`, tightest bound `|r − 1| ≤ 0.217`), while a
*per-`N`* overdispersion `D = 1.61 [1.50, 1.73]` and a QR-dial correlation were
observed at the low-`u` face.

The mechanism behind both observations is completely local and completely
computable: for a prime `p` the polynomial `x² − N` hits `0 mod p` on

  `dial p N := #{x ∈ ZMod p | x² = N}`

residues instead of the "random" single residue.  This file computes the
distribution of that dial exactly.

## Main results

* `dial_of_sq`, `dial_eq_two_iff`, `dial_eq_zero_iff`, `dial_zero` — the
  **dichotomy**: for an odd prime `p` the dial is `2` on nonzero squares, `0` on
  nonsquares, and `1` at `N = 0`.
* `sum_dial` — **first moment is exactly random**: `∑_N dial p N = p`, i.e. the
  dial has mean exactly `1`, the same local density as a random integer.  This
  is the exact statement that quadratic structure gives *no* first-order
  smoothness edge.
* `sum_dial_sq` — **second moment**: `∑_N (dial p N)² = 2p − 1`.
* `localFactor` — the induced multiplicative correction
  `(p − dial p N)/(p − 1)` to the local non-divisibility density, and
  `sum_localFactor` (mean exactly `1`), `sum_localFactor_sq`
  (`= p + 1/(p−1)`), and `sum_localFactor_centred_sq` (variance exactly
  `1/(p(p−1))` per prime).

The variance `1/(p(p−1))` is the seed of the observed per-`N` overdispersion;
it is summed over primes in `Catalog.NumberTheory.ScaleSmoothnessDispersion`.
-/

open ScaleSmoothness

open Finset


theorem dial_def (p : ℕ) [NeZero p] (N : ZMod p) :
    dial p N = #(univ.filter fun x : ZMod p => x ^ 2 = N) := rfl


variable (p : ℕ) [Fact p.Prime]


/-- In an odd prime characteristic `2 ≠ 0`. -/
theorem two_ne_zero_of_ne_two (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have h : ((2 : ℕ) : ZMod p) = 0 ↔ p ∣ 2 := CharP.cast_eq_zero_iff (ZMod p) p 2
  simp only [Nat.cast_ofNat] at h
  intro hzero
  exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 (h.1 hzero))

theorem neg_eq_self_iff (hp : p ≠ 2) {x : ZMod p} : x = -x ↔ x = 0 := by
  constructor
  · intro h
    have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact absurd h' (two_ne_zero_of_ne_two p hp)
    · exact h'
  · rintro rfl; simp

/-- The root set of `x² = c²` is `{c, -c}`. -/
theorem sq_root_set (x : ZMod p) :
    (univ.filter fun y : ZMod p => y ^ 2 = x ^ 2) = {x, -x} := by
  ext y
  simp [sq_eq_sq_iff_eq_or_eq_neg]

/-- **Dichotomy at a square.**  The dial equals `2` at every nonzero square and
`1` at `0`. -/
theorem dial_of_sq (hp : p ≠ 2) (x : ZMod p) :
    dial p (x ^ 2) = if x = 0 then 1 else 2 := by
  rw [dial_def, sq_root_set]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [if_neg hx, card_insert_of_notMem, card_singleton]
    simp only [mem_singleton]
    intro h
    exact hx ((neg_eq_self_iff p hp).1 h)







/-! ### Moments of the dial -/




/-! ### The multiplicative local correction factor -/











open ScaleSmoothness in
theorem solution(hp : p ≠ 2) {N : ZMod p} (hN : N ≠ 0) :
    dial p N = 2 ↔ IsSquare N := by
  constructor
  · intro h
    by_contra hsq
    rw [dial_eq_zero_of_not_isSquare p hsq] at h
    exact absurd h (by norm_num)
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; exact hN (by simp)
    have : r * r = r ^ 2 := by ring
    rw [this, dial_of_sq p hp, if_neg hr]
