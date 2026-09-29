-- Prove2me | solution 1 for PlusOneWilliams.lucasV_eq_two_of_nonsquare_disc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:19:51.865587+00:00
-- url     : https://prove2.me/submissions/c5f23d66-c0cc-4314-bc22-4ba1ce52f716

-- Sol generated from Tropical/PlusOneWilliamsCore.lean
import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore
import Theorems.Thm_PlusOneWilliams_lucasV_eq_two_aux

/-!
# The Williams `p + 1` method: Lucas sequences and the discriminant gate

This file formalises the *arithmetic core* of the round-16 experiment
`PLUSONE-SMOOTH-NULL` (paper 64). The experiment measured, over 40 matched
semiprime pairs, that the classical Williams `p + 1` method (bases `P = 3, 5, 7`,
exponent `M = lcm(1..100)`) factors the `PLUSONE` class 24/40 and the `GENERAL`
class 0/40, and — the new structural finding — that the per-base success set is
*exactly* the set of instances with `(D | p) = -1`, where `D = P² - 4` is the
discriminant of the Lucas sequence.

Here we prove the theorems behind those numbers.

* `lucasV` — the Lucas `V`-sequence with parameters `(P, Q = 1)`, over any
  commutative ring; `lucasV_eq_pow_add_pow` is its Binet form.
* `lucasV_eq_two_of_nonsquare_disc` — **the `p + 1` half of the gate.** If
  `D = P² - 4` is a non-square mod the odd prime `p` and `(p + 1) ∣ M`, then
  `V_M ≡ 2 (mod p)`. The proof builds the quadratic extension
  `𝔽_p[X]/(X² - D) ≅ 𝔽_{p²}`, exhibits the two conjugate roots
  `a, b = (P ± √D)/2` of `x² - Px + 1`, and shows the Frobenius swaps them, so
  `a^{p+1} = ab = 1`.
* `lucasV_eq_two_of_square_disc` — **the `p - 1` half of the gate.** If `D` is a
  square mod `p` the roots are already in `𝔽_p`, so the relevant order divides
  `p - 1`, not `p + 1`: the method silently degenerates to Pollard `p - 1`.
  This is why the observed success rate equals the `(D | p) = -1` rate exactly.
* `williams_gcd_eq_factor` — the gcd step really returns the factor `p`.
* `lucasV_two_eq_two`, `plusOne_base_two_degenerate` — the base `P = 2` has
  `D = 0` and the sequence is constant `2`, so the gcd is always `N`: the
  degenerate base observed in the experiment.
* `legendreSym_fortyfive_eq_five`, `base_three_seven_same_gate` — `D₃ = 5` and
  `D₇ = 45 = 5 · 3²` lie in the same square class, so bases `3` and `7` succeed
  on *exactly* the same primes (observed: 11/40 for both, on the same instances).
-/

open PlusOneWilliams

open Polynomial

/-! ## 1. The Lucas `V`-sequence with `Q = 1` -/









/-! ## 2. The `p + 1` half of the discriminant gate -/




/-! ## 3. The `p - 1` half of the gate: a square discriminant degenerates -/






/-! ## 4. The gcd step returns the factor -/


/-! ## 5. Smoothness feeds the exponent: `p + 1` powersmooth ⇒ `(p+1) ∣ M` -/




/-! ## 6. The degenerate base `P = 2` (`D = 0`) -/




/-! ## 7. Bases 3 and 7 share a square class -/




open PlusOneWilliams in
theorem solution(p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p)
    (hD : ¬ IsSquare (P ^ 2 - 4)) {M : ℕ} (hM : (p + 1) ∣ M) :
    lucasV P M = 2 := by
  classical
  have hp' : p.Prime := Fact.out
  have hD0 : (P ^ 2 - 4 : ZMod p) ≠ 0 := fun h => hD ⟨0, by rw [h]; ring⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hDpow : (P ^ 2 - 4 : ZMod p) ^ (p / 2) = -1 := by
    have hdi := FiniteField.pow_dichotomy hchar hD0
    rw [ZMod.card] at hdi
    rcases hdi with h | h
    · exact absurd ((ZMod.euler_criterion p hD0).2 h) hD
    · exact h
  have hirr : Irreducible (X ^ 2 - C (P ^ 2 - 4 : ZMod p)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hD ⟨b, by rw [← hb]; ring⟩)
  letI : Fact (Irreducible (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) := ⟨hirr⟩
  letI : CharP (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) p :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod p) (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p)))).injective p
  have hs2 : (AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) ^ 2 =
      algebraMap (ZMod p) _ (P ^ 2 - 4) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    exact h
  have hpodd : p = 2 * (p / 2) + 1 := by
    rcases hp'.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hsp : (AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) ^ p =
      -(AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) := by
    set s := AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))
    calc s ^ p = (s ^ 2) ^ (p / 2) * s := by rw [← pow_mul, ← pow_succ, ← hpodd]
      _ = algebraMap (ZMod p) _ ((P ^ 2 - 4 : ZMod p) ^ (p / 2)) * s := by rw [hs2, map_pow]
      _ = -s := by rw [hDpow]; simp
  exact lucasV_eq_two_aux hp2 (algebraMap (ZMod p) _)
    (algebraMap (ZMod p) (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p)))).injective P _ hs2 hsp hM
