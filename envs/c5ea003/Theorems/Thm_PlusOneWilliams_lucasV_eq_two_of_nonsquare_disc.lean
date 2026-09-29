-- Prove2me | Theorems.Thm_PlusOneWilliams_lucasV_eq_two_of_nonsquare_disc
-- name    : PlusOneWilliams.lucasV_eq_two_of_nonsquare_disc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:37:30.256638+00:00
-- url     : https://prove2.me/theorems/65433ce0-037c-49ba-9473-909e5d414e9c
-- title:
--   The `p + 1` half of the discriminant gate.
-- statement:
--   **The `p + 1` half of the discriminant gate.** For an odd prime `p` and a
--   base `P` whose discriminant `D = P² - 4` is a non-square mod `p`, the Lucas
--   sequence satisfies `V_M ≡ 2 (mod p)` for every exponent `M` divisible by
--   `p + 1`. This is the correctness statement of the Williams (1982) method.
--
--   ```lean
--   theorem PlusOneWilliams.lucasV_eq_two_of_nonsquare_disc(p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p)
--       (hD : ¬ IsSquare (P ^ 2 - 4)) {M : ℕ} (hM : (p + 1) ∣ M) :
--       lucasV P M = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/PlusOneWilliamsCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/PlusOneWilliamsCore.lean#L152

-- Thm stub generated from Tropical/PlusOneWilliamsCore.lean
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

theorem PlusOneWilliams.lucasV_eq_two_of_nonsquare_disc(p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p)
    (hD : ¬ IsSquare (P ^ 2 - 4)) {M : ℕ} (hM : (p + 1) ∣ M) :
    lucasV P M = 2 := by sorry
