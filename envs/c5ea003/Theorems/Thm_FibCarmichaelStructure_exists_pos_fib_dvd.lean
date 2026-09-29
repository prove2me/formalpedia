-- Prove2me | Theorems.Thm_FibCarmichaelStructure_exists_pos_fib_dvd
-- name    : FibCarmichaelStructure.exists_pos_fib_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:48:37.886349+00:00
-- url     : https://prove2.me/theorems/08390e63-3f99-49aa-92ec-8d4768a4de9a
-- title:
--   Exists pos fib dvd
-- statement:
--   Formal statement of `FibCarmichaelStructure.exists_pos_fib_dvd` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibCarmichaelStructure.exists_pos_fib_dvd(p : ℕ) (hp : 1 ≤ p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FibCarmichaelStructure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FibCarmichaelStructure.lean#L109

-- Thm stub generated from Novelty/FibCarmichaelStructure.lean
import Mathlib
import Definitions.Def_Novelty_FibCarmichaelStructure
import Definitions.Def_Novelty_FibonacciEntryPointDuality

/-!
# Structure of the Fibonacci rank of apparition

This file **deepens** `Catalog/Novelty/FibonacciEntryPointDuality.lean`.  There the master
*duality* was proven,
`p ∣ F n ↔ z(p) ∣ n`,  where `z(p) = fibEntry p` is the rank of apparition (entry point).
That biconditional turns a divisibility question about Fibonacci numbers into a divisibility
question about the single arithmetic function `z`.  Here we develop the **multiplicative
structure** of `z` that the duality unlocks, and we settle the classical existence theorem
that makes `z` total.

## Main results

* `exists_pos_fib_dvd` — **the rank of apparition exists**: for every `p ≥ 1` there is a
  positive index `k` with `p ∣ F k`.  This is the classical theorem (Fibonacci is purely
  periodic modulo `p`) and is *not* in Mathlib; we prove it from scratch by viewing the pair
  `(F k, F (k+1))` as the orbit of an invertible linear map on the finite ring `ZMod p × ZMod p`.
* `fibEntry_pos` — consequently `z(p) > 0` for all `p ≥ 1`: the entry point is genuinely total.
* `fib_dvd_gcd_iff` — **simultaneous apparition collapses to the gcd**:
  `p ∣ F (gcd m n) ↔ p ∣ F m ∧ p ∣ F n`.
* `fibEntry_coprime_mul` — **the lcm law** (centerpiece): for coprime `m, n`,
  `z(m·n) = lcm (z m) (z n)`.  The entry point of a coprime product is the lcm of the parts;
  `z` behaves like a "Carmichael λ-function" for the Fibonacci sequence.
* `fibEntry_prod_coprime` — the lcm law for an arbitrary **pairwise-coprime finite product**,
  `z(∏ f i) = lcm_i z(f i)`, recombining via the same squarefree/coprime mechanism that drives
  the Korselt identity in `Catalog/Novelty/KorseltCarmichael.lean`.
* `fibEntry_squarefree` — for squarefree `n`, `z(n) = lcm` of `z(p)` over the prime factors `p ∣ n`.

## Catalog synthesis

This unifies two catalog threads.  From `FibonacciEntryPointDuality` it inherits `fibEntry`,
`fib_dvd_iff_fibEntry_dvd`, and `fib_dvd_gcd`; the new content is that the *universal* duality
forces `z` to be a lattice morphism (gcd ↦ ⋀, coprime product ↦ lcm).  From
`KorseltCarmichael` it borrows the squarefree pairwise-coprime recombination idea
(`Nat.prod_primeFactors_of_squarefree` + pairwise coprimality of distinct primes), now applied
to apparition ranks rather than to `a^n - a`.  The existence theorem `exists_pos_fib_dvd`
removes the only standing hypothesis ("an entry point exists") that the duality file had to
work around at the `n = 0` boundary.

-- !-- Lab Notebook -- !--
-- !-- Hypothesis: the entry point `z = fibEntry` is a *morphism of divisibility lattices*:
--     it sends gcd to meet and coprime products to lcm, and it is total on `p ≥ 1`. -- !--
-- !-- Result: proved totality (`exists_pos_fib_dvd`, `fibEntry_pos`), the meet law
--     (`fib_dvd_gcd_iff`), the binary lcm law (`fibEntry_coprime_mul`), its finite
--     pairwise-coprime generalization (`fibEntry_prod_coprime`), and the squarefree
--     specialization (`fibEntry_squarefree`). -- !--
-- !-- Insight: the universal duality `p ∣ F n ↔ z(p) ∣ n` means the divisibility set
--     `{n | p ∣ F n}` is *exactly* the principal ideal `(z p)`.  An identity of principal
--     ideals is an identity of generators, so every lattice identity among these sets
--     descends verbatim to `z`.  The lcm law is then `lcm_dvd_iff` + `Coprime.mul_dvd`. -- !--
-- !-- Insight: totality is purely homotopical/dynamical — the apparition index is the first
--     return time of the orbit of `(0,1)` under the invertible "Fibonacci shift" on the
--     finite phase space `ZMod p × ZMod p`; invertibility forces pure periodicity. -- !--
-- !-- Failure analysis: `decide` cannot evaluate `fibEntry` (it is `Nat.find` behind
--     `Classical`); all proofs route through the duality, never through computation. The
--     generator-uniqueness lemma `dvd_eq_of_dvd_iff` is what makes the lattice transfer
--     formal rather than heuristic. -- !--
-- !-- End Lab Notebook -- !--
-/

open FibCarmichaelStructure

open FibEntryDuality




/-
!-- One step of the phase orbit is the shift applied to the current pair, since
`F (k+2) = F k + F (k+1)` (`Nat.fib_add_two`) descends to `ZMod p`. -- !--
-/

/-
!-- The phase point at index `k` is the `k`-fold shift of the initial pair `(0,1)`. -- !--
-/

/-
**Existence of the rank of apparition.** For every `p ≥ 1` some positive Fibonacci index
is divisible by `p`.

!-- The orbit `k ↦ fibPair p k` lands in the finite set `ZMod p × ZMod p`, so by pigeonhole
two indices `i < j` collide; the shift is injective, so cancelling `i` steps gives
`fibPair p (j-i) = fibPair p 0 = (0,1)`, whence `p ∣ F (j-i)` with `j-i > 0`. -- !--
-/

theorem FibCarmichaelStructure.exists_pos_fib_dvd(p : ℕ) (hp : 1 ≤ p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by sorry
