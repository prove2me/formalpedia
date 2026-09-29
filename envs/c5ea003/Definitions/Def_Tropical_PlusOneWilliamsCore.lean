-- Prove2me | Definitions.Def_Tropical_PlusOneWilliamsCore
-- name    : Tropical_PlusOneWilliamsCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:19.635664+00:00
-- url     : https://prove2.me/theorems/95556bca-d5ca-415e-8af2-d8b92e5c5024
-- title:
--   Aether Catalog definitions — Tropical_PlusOneWilliamsCore
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.PlusOneWilliamsCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/PlusOneWilliamsCore.lean by skeleton subtraction
import Mathlib

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

namespace PlusOneWilliams

open Polynomial

/-! ## 1. The Lucas `V`-sequence with `Q = 1` -/

/-- The Lucas `V`-sequence `V₀ = 2`, `V₁ = P`, `V_{n+2} = P·V_{n+1} - V_n`
(parameters `(P, Q = 1)`), over an arbitrary commutative ring. -/
def lucasV {R : Type*} [CommRing R] (P : R) : ℕ → R
  | 0 => 2
  | 1 => P
  | (n + 2) => P * lucasV P (n + 1) - lucasV P n








/-! ## 2. The `p + 1` half of the discriminant gate -/




/-! ## 3. The `p - 1` half of the gate: a square discriminant degenerates -/






/-! ## 4. The gcd step returns the factor -/


/-! ## 5. Smoothness feeds the exponent: `p + 1` powersmooth ⇒ `(p+1) ∣ M` -/

/-- The classical Williams exponent `M = lcm(1, …, B)` (the experiment used
`B = 100`). -/
def lcmUpTo (B : ℕ) : ℕ := (Finset.Icc 1 B).lcm id



/-! ## 6. The degenerate base `P = 2` (`D = 0`) -/




/-! ## 7. Bases 3 and 7 share a square class -/



end PlusOneWilliams


