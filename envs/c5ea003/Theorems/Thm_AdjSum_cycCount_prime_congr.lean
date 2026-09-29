-- Prove2me | Theorems.Thm_AdjSum_cycCount_prime_congr
-- name    : AdjSum.cycCount_prime_congr
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:14:26.390738+00:00
-- url     : https://prove2.me/theorems/7156998a-7de3-4c2a-b57c-ade5a2ed9b48
-- title:
--   Prime Gauss congruence for the adjacent-sum model.
-- statement:
--   **Prime Gauss congruence for the adjacent-sum model.**  For a prime length `p = q+1`,
--   the number of cyclic adjacent-sum lattice points is congruent, modulo `p`, to the number
--   of constant ones, i.e. to `tr (adjMat s) = ⌊s/2⌋ + 1`.
--
--   ```lean
--   theorem AdjSum.cycCount_prime_congr(s q : ℕ) (hp : Nat.Prime (q + 1)) :
--       cycCount s q ≡ s / 2 + 1 [MOD q + 1] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/Necklace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/Necklace.lean#L147

-- Thm stub generated from Applications/AdjacentSumPolytopes/Necklace.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# Rotation action, Möbius recurrence, and a Gauss congruence

The cyclic adjacent-sum lattice points of length `n` carry an action of the cyclic group
of order `n` by rotation of coordinates.  When `n = p` is prime, the fixed-point formula
for `p`-groups yields a congruence between the cyclic count and the number of *constant*
points, i.e. the trace of the transfer matrix itself:

`#(cyclic points of length p) ≡ ⌊s/2⌋ + 1 = tr (adjMat s)  (mod p)`.

This is the first instance of the Gauss congruence `tr(Mⁿ) ≡ ∑_{d ∣ n} μ(n/d) tr(M^d) ≡ 0
(mod n)` for the transfer matrix, and it is exactly the statement that the *primitive*
(aperiodic) cyclic points of prime length come in orbits of size `p`.

We also set up the **Möbius recurrence** for the cyclic counts: the primitive counts
`primCyc s n = ∑_{(a,b) : ab = n} μ(a) · tr(M^b)` satisfy
`∑_{d ∣ n} primCyc s d = tr(Mⁿ)` for all `n > 0`, and `p ∣ primCyc s p` for `p` prime.

-- !-- Lab Notes -- !--
* **Hypothesis.** Rotation of a cyclic adjacent-sum point is again one; for prime length
  the only rotation-fixed points are the constant ones, which are exactly the "core"
  states `2a ≤ s`.  Hence the prime congruence.
* **Experiment.** `s = 2`, where `tr(adjMat 2) = ⌊2/2⌋ + 1 = 2`.  The cyclic counts for
  lengths `1..7` are `2, 6, 11, 26, 57, 129, 289`.  At the prime lengths:
  `tr(M²) = 6 ≡ 0 ≡ 2 (mod 2)`, `tr(M³) = 11 = 3·3 + 2 ≡ 2 (mod 3)`,
  `tr(M⁵) = 57 = 11·5 + 2 ≡ 2 (mod 5)`, `tr(M⁷) = 289 = 41·7 + 2 ≡ 2 (mod 7)` — all
  congruent to `tr(M) = 2`, as predicted.  Note the indexing: `cycCount s d` is the
  count for length `d + 1`.
* **Analysis.** The congruence survives; the primes are exactly where the fixed-point
  formula applies with no extra bookkeeping, and the general `n` case requires the full
  necklace/orbit decomposition, recorded as a conjecture.
* **Critique.** The proof is not vacuous: the fixed-point set is genuinely computed
  (`fixEquiv`), and it is nonempty (the origin is always a point), so the congruence has
  content on both sides.
-/

open AdjSum

open Finset Matrix

/-! ## The trace of the transfer matrix counts the core states -/


/-! ## The rotation action on cyclic points -/







/-! ## The prime congruence -/

theorem AdjSum.cycCount_prime_congr(s q : ℕ) (hp : Nat.Prime (q + 1)) :
    cycCount s q ≡ s / 2 + 1 [MOD q + 1] := by sorry
