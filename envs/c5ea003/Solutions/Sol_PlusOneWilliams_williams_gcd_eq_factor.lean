-- Prove2me | solution 1 for PlusOneWilliams.williams_gcd_eq_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:24:13.546752+00:00
-- url     : https://prove2.me/submissions/cef4e6af-4631-4a89-b1db-5207b87e8f6a

-- Sol generated from Tropical/PlusOneWilliamsCore.lean
import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {V : ℤ}
    (hpV : (p : ℤ) ∣ V) (hqV : ¬ (q : ℤ) ∣ V) :
    Int.gcd V ((p * q : ℕ) : ℤ) = p := by
  have hpg : p ∣ Int.gcd V ((p * q : ℕ) : ℤ) :=
    Int.dvd_gcd hpV ⟨(q : ℤ), by push_cast; ring⟩
  have hgN : Int.gcd V ((p * q : ℕ) : ℤ) ∣ p * q := by
    have h : (Int.gcd V ((p * q : ℕ) : ℤ) : ℤ) ∣ ((p * q : ℕ) : ℤ) :=
      Int.gcd_dvd_right V ((p * q : ℕ) : ℤ)
    exact_mod_cast h
  obtain ⟨m, hm⟩ := hpg
  rw [hm] at hgN
  have hmq : m ∣ q := (mul_dvd_mul_iff_left hp.ne_zero).mp hgN
  have hgV : (Int.gcd V ((p * q : ℕ) : ℤ) : ℤ) ∣ V := Int.gcd_dvd_left V ((p * q : ℕ) : ℤ)
  rcases hq.eq_one_or_self_of_dvd m hmq with hm1 | hm1
  · rw [hm, hm1, mul_one]
  · exfalso
    refine hqV (dvd_trans ?_ hgV)
    rw [hm, hm1]
    exact ⟨(p : ℤ), by push_cast; ring⟩
