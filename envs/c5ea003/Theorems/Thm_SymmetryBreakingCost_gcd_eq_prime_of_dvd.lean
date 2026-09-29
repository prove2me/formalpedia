-- Prove2me | Theorems.Thm_SymmetryBreakingCost_gcd_eq_prime_of_dvd
-- name    : SymmetryBreakingCost.gcd_eq_prime_of_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:38:56.76092+00:00
-- url     : https://prove2.me/theorems/24bded01-d80d-4e1f-9d33-86da3164741c
-- title:
--   If `w` is divisible by `p` but not by `q` (both prime), its gcd with `p q` is exactly `p`.
-- statement:
--   If `w` is divisible by `p` but not by `q` (both prime), its gcd with `p q` is exactly `p`.
--
--   ```lean
--   theorem SymmetryBreakingCost.gcd_eq_prime_of_dvd{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : ℤ} (hpw : (p : ℤ) ∣ w)
--       (hqw : ¬(q : ℤ) ∣ w) : Int.gcd w ((p * q : ℕ) : ℤ) = p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SymmetryBreakingCostWitness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SymmetryBreakingCostWitness.lean#L91

-- Thm stub generated from Novelty/SymmetryBreakingCostWitness.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostKernel

/-!
# The witness always exists: information present, search sealed

Cycles 1–3 measured the two classical resources.  This fourth cycle closes the loop on the
*asymmetric* side by showing that the object Shor's algorithm hunts for is never missing:

* `exists_nontrivial_sqrt_one` : every odd semiprime `N = p q` admits an explicit `x` with
  `x² ≡ 1 (mod N)` and `x ≢ ±1 (mod N)` — built by the Chinese remainder theorem, exactly the
  same freedom that makes the residue oracle cheap.
* `gcd_witness_eq_prime` : for that witness, `gcd(x - 1, N) = p` **on the nose**; one gcd
  recovers the factor.
* `factor_of_any_nontrivial_sqrt` : conversely *every* nontrivial square root of `1` mod `N`
  factors `N` — `gcd(z - 1, N)` is `p` or `q`, there is no third kind of witness.
* `symmetry_breaking_cost_table` : the three measurements side by side for an odd semiprime —
  the oracle cost is exactly `⌈log₂ |S|⌉`, the public battery excludes no candidate at all, and
  an asymmetric witness that factors `N` in one gcd exists.

The moral of the measurement: for every odd semiprime, factoring data is *present* in the
arithmetic (a residue signature isolating `p₀` in `⌈log₂ |S|⌉` bits, a square root of unity
revealing `p` in one gcd).  What is missing is a symmetry-breaking *resource* that points at it;
the classical public data `[(a | N)]` is provably blind (cycle 2), and this is what the quantum
order-finding channel buys.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 4): the nontrivial square roots of unity are never rare or
absent — the obstruction is purely search, never existence.

Experiment (Experimenter): for `(p, q) = (3,5), (3,7), (3,11), (5,7), (7,11), (11,13)` the CRT
witness `x ≡ 1 mod p`, `x ≡ -1 mod q` is `x = 4, 13, 10, 6, 43, 12`; in every case `x² ≡ 1 mod
N` and `gcd(x - 1, N) = p`, i.e. `3, 3, 3, 5, 7, 11`, confirming the two theorems below on
concrete inputs.

Analysis (Analyst): the construction and the oracle construction of cycle 1 are the *same*
mechanism — prescribing independent local data and gluing by CRT.  What differs is whether the
prescribed data is readable from `N`: the local Legendre symbols and the local square roots are
both invisible to the symmetric battery, by the kernel theorem of cycle 2.

Critique (Critic): `gcd_witness_eq_prime` must not be vacuous, so the witness is produced
explicitly rather than assumed, and the hypotheses are only `p ≠ q` odd primes; the numerical
run above checks the statement on six semiprimes.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols

theorem SymmetryBreakingCost.gcd_eq_prime_of_dvd{p q : ℕ} (hp : p.Prime) (hq : q.Prime) {w : ℤ} (hpw : (p : ℤ) ∣ w)
    (hqw : ¬(q : ℤ) ∣ w) : Int.gcd w ((p * q : ℕ) : ℤ) = p := by sorry
