-- Prove2me | Theorems.Thm_BinomialGCDA080170_prime_dvd_choose_primePow
-- name    : BinomialGCDA080170.prime_dvd_choose_primePow
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:05:37.306775+00:00
-- url     : https://prove2.me/theorems/37de61a9-e48b-4c7d-ac9a-f83847bf6a51
-- title:
--   Prime dvd choose primePow
-- statement:
--   Formal statement of `BinomialGCDA080170.prime_dvd_choose_primePow` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BinomialGCDA080170.prime_dvd_choose_primePow{p a q : ℕ} (hp : p.Prime)
--       (hq2 : 2 ≤ q) (hqp : q ≤ p ^ a) :
--       p ∣ Nat.choose (q * (p ^ a - 1)) (p ^ a - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BinomialGCDA080170PrimePower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BinomialGCDA080170PrimePower.lean#L50

-- Thm stub generated from Novelty/BinomialGCDA080170PrimePower.lean
import Mathlib
import Definitions.Def_Novelty_BinomialGCDA080170

/-!
# The prime-power fibre of OEIS A080170

This companion file extends `Catalog.Novelty.BinomialGCDA080170`.  There the
prime fibre `n = p` was analysed; here we treat the full *prime-power* fibre
`n = p^a`.

The main result `prime_dvd_binomGCD_primePow` shows that for every prime power
`p^a` (with `a ≥ 1`) the binomial gcd `D(p^a - 1)` is divisible by `p`, hence
is nontrivial.  This is the divisibility heart of the (computationally
verified) identity `D(p^a - 1) = p^a`, which is exactly the regime where
Ralf Stephan's closed form *is* correct (see `FUTURE_DIRECTIONS.md`).

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  On the prime-power fibre `n = p^a` the gcd should
remain divisible by `p` for every `a`, not just `a = 1`.

EXPERIMENT (Experimenter).  Verified `p ∣ C(q(p^a-1), p^a-1)` for all
`2 ≤ q ≤ p^a` over many `(p, a)` (see `ComputationalEvidence.md`), and proved
it with Kummer's theorem.

ANALYSIS (Analyst).  The key is a *carry at level* `i = v_p(q-1) + 1`.  Since
`p^a - 1 ≡ -1 (mod p^i)` for `i ≤ a`, we have `(p^a-1) % p^i = p^i - 1`, and
`(q-1)(p^a-1) ≡ -(q-1) (mod p^i)`.  Choosing `i` one above the `p`-adic
valuation of `q-1` guarantees `p^i ∤ (q-1)`, so the residue
`(-(q-1)) % p^i ≥ 1` and the carry condition `p^i ≤ (p^i-1) + ((-(q-1)) % p^i)`
holds.  This single carry yields `p ∣ C(q(p^a-1), p^a-1)`.

CRITIQUE (Critic).  The exponent bound `i ≤ a` is essential and uses
`q - 1 < p^a` (from `q ≤ p^a`); without it the residue identity for
`p^a - 1` fails.  The proof is uniform in `q` and `a`, not a finite check.

SYNTHESIS (PI).  Combined with the `a = 1` exactness `p² ∤ D(p-1)` of the
parent file, this pins the qualitative behaviour of `D` on prime powers and
isolates exactly where Stephan's formula succeeds.
-/

open BinomialGCDA080170

open Nat Finset

/-
**Kummer lower bound, prime-power form.**  For a prime `p` and `2 ≤ q ≤ p^a`,
the prime `p` divides `C(q·(p^a - 1), p^a - 1)`.  A carry occurs in base `p` at
digit `v_p(q-1) + 1`.  (For `a = 0` the hypotheses `2 ≤ q ≤ 1` are unsatisfiable,
so no lower bound on `a` is needed.)
-/

theorem BinomialGCDA080170.prime_dvd_choose_primePow{p a q : ℕ} (hp : p.Prime)
    (hq2 : 2 ≤ q) (hqp : q ≤ p ^ a) :
    p ∣ Nat.choose (q * (p ^ a - 1)) (p ^ a - 1) := by sorry
