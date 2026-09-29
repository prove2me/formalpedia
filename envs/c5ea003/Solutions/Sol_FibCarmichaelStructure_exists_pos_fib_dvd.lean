-- Prove2me | solution 1 for FibCarmichaelStructure.exists_pos_fib_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:49:40.58306+00:00
-- url     : https://prove2.me/submissions/dcba571c-4dde-4d10-81f8-85c03a58d9bd

-- Sol generated from Novelty/FibCarmichaelStructure.lean
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

/-
**Squarefree specialization.** For squarefree `n`, the rank of apparition is the lcm of the
ranks of its prime factors: `z(n) = lcm_{p ∣ n} z(p)`.

!-- Rewrite `n = ∏ p ∈ n.primeFactors, p` (`Nat.prod_primeFactors_of_squarefree`) and apply
`fibEntry_prod_coprime`; distinct primes are coprime (`Nat.coprime_primes`). -- !--
-/


open FibCarmichaelStructure in
theorem solution(p : ℕ) (hp : 1 ≤ p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by
  by_cases hp1 : p = 1;
  · exact ⟨ 1, by norm_num [ hp1 ] ⟩;
  · -- Consider the sequence of pairs $(F_n \mod p, F_{n+1} \mod p)$. Since there are only $p^2$ possible pairs, by the pigeonhole principle, there exist indices $i < j$ such that $(F_i \mod p, F_{i+1} \mod p) = (F_j \mod p, F_{j+1} \mod p)$.
    obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : ℕ, i < j ∧ (Nat.fib i % p = Nat.fib j % p ∧ Nat.fib (i + 1) % p = Nat.fib (j + 1) % p) := by
      have h_finite : Set.Finite (Set.range (fun n => (Nat.fib n % p, Nat.fib (n + 1) % p))) := by
        exact Set.finite_iff_bddAbove.mpr ⟨ ⟨ p - 1, p - 1 ⟩, by rintro a ⟨ n, rfl ⟩ ; exact ⟨ Nat.le_sub_one_of_lt ( Nat.mod_lt _ hp ), Nat.le_sub_one_of_lt ( Nat.mod_lt _ hp ) ⟩ ⟩;
      contrapose! h_finite;
      exact Set.infinite_range_of_injective fun i j hij => le_antisymm ( le_of_not_gt fun hi => h_finite _ _ hi ( by aesop ) ( by aesop ) ) ( le_of_not_gt fun hj => h_finite _ _ hj ( by aesop ) ( by aesop ) );
    induction' i with i ih generalizing j;
    · exact ⟨ j, hij, Nat.dvd_of_mod_eq_zero <| by simpa using h_eq.1.symm ⟩;
    · specialize ih ( j - 1 ) ( Nat.lt_pred_iff.mpr hij ) ; rcases j <;> simp_all +decide [ Nat.fib_add_two, Nat.add_mod ];
      simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ];
      aesop
