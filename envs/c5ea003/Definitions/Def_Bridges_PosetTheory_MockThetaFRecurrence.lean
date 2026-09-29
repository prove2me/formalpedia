-- Prove2me | Definitions.Def_Bridges_PosetTheory_MockThetaFRecurrence
-- name    : Bridges_PosetTheory_MockThetaFRecurrence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:32:17.158794+00:00
-- url     : https://prove2.me/theorems/dde3d356-5418-4ecc-9c1f-e73d5fc88897
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_MockThetaFRecurrence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.MockThetaFRecurrence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/MockThetaFRecurrence.lean by skeleton subtraction
import Mathlib

/-! # A Number-Theory ⋈ Holonomy Bridge: Ramanujan's third order mock theta f(q)

This file investigates the claim (Phase A research prompt v16):

> The coefficients `a_n` in `f(q) = ∑_{n≥0} a_n q^n` (Ramanujan's third order mock
> theta function `f(q) = ∑_{n≥0} q^{n^2} / ∏_{k=1}^n (1+q^k)^2`) satisfy
> `(n+3) a_{n+3} = (3n+4) a_{n+2} - (3n+1) a_{n+1} + n a_n` for all `n ≥ 0`,
> with `a_0 = 1, a_1 = 0, a_2 = 1`.

**Both halves of the claim are false.**  The genuine coefficients of `f(q)` are the
integer sequence OEIS A000025 `1, 1, -2, 3, -3, 3, -5, 7, -6, 6, ...`, so the stated
initial data `(a_0,a_1,a_2) = (1,0,1)` is already wrong (the true triple is
`(1, 1, -2)`).  Moreover, *the recurrence with the stated initial data has no integer
solution at all*: it forces `3 a_3 = 4`, i.e. `a_3 = 4/3 ∉ ℤ`.  Since the genuine
coefficients of `f(q)` are integers, the recurrence-with-initials simply cannot
describe them.

This is the "Bridges" content: it connects elementary number theory (integrality of
the q-expansion of a mock theta function) to the *holonomy* of a sequence (existence
of a polynomial-coefficient linear recurrence, i.e. P-recursiveness).  Mock theta
functions are famously **non-holonomic**, so no finite linear recurrence with
polynomial coefficients can hold — consistent with our computational search finding no
recurrence of order ≤ 5 and polynomial degree ≤ 5.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):
  H1. The stated recurrence + initials describes the f(q) coefficients.            [tested]
  H2. The stated initials (1,0,1) are the true coefficients.                        [tested]
  H3. The stated recurrence has *some* integer solution with these initials.     [tested]
  H4. f(q)'s coefficients satisfy *some* low-order polynomial recurrence.           [tested, computational]

Experiment (Experimenter):
  * Computed f(q) coefficients to order 60 by formal power-series division:
      1, 1, -2, 3, -3, 3, -5, 7, -6, 6, -10, 12, -11, 13, -17, 20, ...  (A000025).
  * Evaluating the stated recurrence on the *stated* initials gives a_3 = 4/3, a_4 = 4/3,
    a_5 = 6/5 — non-integers.  → refutes H1, H3.
  * The true initials are (1,1,-2), not (1,0,1).                          → refutes H2.
  * Gaussian elimination over ℚ found NO nonzero polynomial recurrence of order r ≤ 5
    and degree d ≤ 5 fitting A000025.                                     → evidence against H4.

Analysis (Analyst):
  * "false" (not "true but hard"): the premise is internally inconsistent.  Over ℤ the
    recurrence's n=0 instance reads `3 a_3 = 4 a_2 - a_1 = 4`, with no integer root.
  * The deep reason H4 fails: mock theta functions are non-holonomic (Andrews et al.),
    so the very *shape* of the claim (a P-recurrence) cannot hold for genuine f(q).

Critique (Critic):
  * The integer-impossibility theorem must not be vacuous: we keep all three stated
    initials as hypotheses and derive a contradiction from a *single* recurrence
    instance, via `omega` on `3 * a 3 = 4`.
  * We additionally pin down the exact rational value forced at index 3 to make the
    non-integrality concrete and machine-checked, not merely asserted.

Synthesis (PI): see the three theorems below + the uniqueness companion file.
-- !-- End Lab Notes -- !--
-/

namespace MockThetaF

/-- The triple `(a n, a (n+1), a (n+2))` produced by running the *claimed* recurrence
`(n+3) a_{n+3} = (3n+4) a_{n+2} - (3n+1) a_{n+1} + n a_n` forward over `ℚ`, starting
from the *claimed* initial data `(a_0,a_1,a_2) = (1,0,1)`. -/
def claimAux : ℕ → ℚ × ℚ × ℚ
  | 0 => (1, 0, 1)
  | (n+1) =>
      ((claimAux n).2.1, (claimAux n).2.2,
        ((3 * (n : ℚ) + 4) * (claimAux n).2.2 - (3 * (n : ℚ) + 1) * (claimAux n).2.1
          + (n : ℚ) * (claimAux n).1) / ((n : ℚ) + 3))

/-- The candidate coefficient sequence forced by the claimed recurrence and initials. -/
def claimSeq (n : ℕ) : ℚ := (claimAux n).1










end MockThetaF


