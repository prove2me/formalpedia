-- Prove2me | solution 3 for fermat_last_theorem
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-20T01:04:04.125552+00:00
-- url     : https://prove2.me/submissions/358d9ebf-002a-4e25-8ab6-1bd063d9378e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_fermat_last_theorem
import Theorems.Thm_bp_flt_for_p_ge_5
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four
import Mathlib.Tactic.IntervalCases

/-!
Sketch 1: reduce FLT to the case of prime exponents p ≥ 5.

Blueprint chapter 2 §2.3: every n ≥ 3 either has an odd prime factor p, in which
case a counterexample for n yields one for p (Mathlib's
`FermatLastTheorem.of_odd_primes`, building on Fermat's `fermatLastTheoremFour`),
or n is a power of 2 ≥ 4, also covered. Euler's `fermatLastTheoremThree` handles
p = 3, leaving primes p ≥ 5 — the child `bp_flt_for_p_ge_5`.
-/

theorem solution (n : ℕ) (hn : 3 ≤ n) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) : a ^ n + b ^ n ≠ c ^ n := by
  have flt : FermatLastTheorem := by
    apply FermatLastTheorem.of_odd_primes
    intro p pp p_odd
    if hp5 : 5 ≤ p then
      intro a' b' c' ha' hb' hc'
      exact bp_flt_for_p_ge_5 p pp hp5 a' b' c'
        (Nat.pos_of_ne_zero ha') (Nat.pos_of_ne_zero hb') (Nat.pos_of_ne_zero hc')
    else
      have hp2 := pp.two_le
      interval_cases p
      · exact absurd p_odd (by decide)
      · exact fermatLastTheoremThree
      · exact absurd pp (by decide)
  exact flt n hn a b c ha.ne' hb.ne' hc.ne'
