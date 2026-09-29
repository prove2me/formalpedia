-- Prove2me | Theorems.Thm_FibCarmichaelStructure_fibEntry_prod_coprime
-- name    : FibCarmichaelStructure.fibEntry_prod_coprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:48:57.304191+00:00
-- url     : https://prove2.me/theorems/1d3a16f2-8687-4bfe-bb1a-78d396a10ed2
-- title:
--   FibEntry prod coprime
-- statement:
--   Formal statement of `FibCarmichaelStructure.fibEntry_prod_coprime` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibCarmichaelStructure.fibEntry_prod_coprime{ι : Type*} (s : Finset ι) (f : ι → ℕ)
--       (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
--       fibEntry (∏ i ∈ s, f i) = s.lcm (fun i => fibEntry (f i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FibCarmichaelStructure.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FibCarmichaelStructure.lean#L181

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

/-
The entry point is **strictly positive** (totally defined) for every `p ≥ 1`.

!-- `fibEntry p = Nat.find h` for the existence witness `h := exists_pos_fib_dvd`; its spec
gives positivity. -- !--
-/

/-
`z(1) = 1`: the entry point of `1` is `1`.

!-- `1 ∣ F 1` and `1` is the least positive index, so `Nat.find` returns `1`. -- !--
-/

/-
**Simultaneous apparition = apparition at the gcd.** `p` divides both `F m` and `F n`
iff it divides `F (gcd m n)`.  (For `p` this is the meet law `z ∣ m ∧ z ∣ n ↔ z ∣ gcd m n`.)

!-- Apply the duality `fib_dvd_iff_fibEntry_dvd` to all three terms and use
`Nat.dvd_gcd_iff : k ∣ gcd m n ↔ k ∣ m ∧ k ∣ n`. -- !--
-/

/-
**The lcm law.** The rank of apparition of a coprime product is the lcm of the ranks:
`z(m·n) = lcm (z m) (z n)` for coprime `m, n`.  No positivity hypothesis is needed because the
duality is universal.

!-- By `dvd_eq_of_dvd_iff` it suffices that for all `k`,
`z(mn) ∣ k ↔ lcm(z m)(z n) ∣ k`.  LHS ↔ `mn ∣ F k` (duality) ↔ `m ∣ F k ∧ n ∣ F k`
(coprime, `Coprime.mul_dvd_of_dvd_of_dvd`) ↔ `z m ∣ k ∧ z n ∣ k` (duality) ↔ RHS
(`Nat.lcm_dvd_iff`). -- !--
-/

/-
**Finite lcm law.** For a pairwise-coprime family `f` over a finset `s`,
`z(∏ f i) = lcm_i z(f i)`.

!-- Induct on `s` with `Finset.induction`: base `z(1) = 1 = Finset.lcm ∅` via `fibEntry_one`;
step uses `fibEntry_coprime_mul` after `Nat.Coprime.prod_right` shows `f a` is coprime to
the product over the rest, and `Finset.lcm_insert`. -- !--
-/

theorem FibCarmichaelStructure.fibEntry_prod_coprime{ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    fibEntry (∏ i ∈ s, f i) = s.lcm (fun i => fibEntry (f i)) := by sorry
