-- Prove2me | solution 1 for FibCarmichaelStructure.fibEntry_prod_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:52:45.356025+00:00
-- url     : https://prove2.me/submissions/395ef755-f99c-4e98-934b-7cfe33fec350

-- Sol generated from Novelty/FibCarmichaelStructure.lean
import Mathlib
import Definitions.Def_Novelty_FibCarmichaelStructure
import Definitions.Def_Novelty_FibonacciEntryPointDuality
import Theorems.Thm_FibEntryDuality_fib_dvd_iff_fibEntry_dvd

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

/-- **Generator uniqueness.** Two naturals with the same principal ideal are equal:
if `a ∣ k ↔ b ∣ k` for all `k`, then `a = b`.  This is the engine that lets divisibility-set
identities descend to identities of entry points. -/
-- !-- Take `k = b` (gives `a ∣ b`) and `k = a` (gives `b ∣ a`), then `Nat.dvd_antisymm`. -- !--
lemma dvd_eq_of_dvd_iff {a b : ℕ} (h : ∀ k, a ∣ k ↔ b ∣ k) : a = b := by
  exact Nat.dvd_antisymm ((h b).mpr dvd_rfl) ((h a).mp dvd_rfl)



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
lemma fibEntry_one : fibEntry 1 = 1 := by
  unfold fibEntry; simp +decide ;
  split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
  cases ‹∀ x : ℕ, x = 0› 1

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
theorem fibEntry_coprime_mul {m n : ℕ} (h : Nat.Coprime m n) :
    fibEntry (m * n) = Nat.lcm (fibEntry m) (fibEntry n) := by
  apply dvd_eq_of_dvd_iff;
  simp +decide [ ← fib_dvd_iff_fibEntry_dvd, Nat.lcm_dvd_iff ];
  exact fun k => ⟨ fun hk => ⟨ dvd_of_mul_right_dvd hk, dvd_of_mul_left_dvd hk ⟩, fun hk => Nat.Coprime.mul_dvd_of_dvd_of_dvd h hk.1 hk.2 ⟩

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
theorem solution{ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j)) :
    fibEntry (∏ i ∈ s, f i) = s.lcm (fun i => fibEntry (f i)) := by
  induction' s using Finset.induction_on with i s hi ih;
  all_goals try exact Classical.decEq _;
  · convert fibEntry_one;
  · by_cases hi' : f i = 0 <;> by_cases hs' : ∏ i ∈ s, f i = 0 <;> simp_all +decide [ Nat.Coprime ];
    · unfold fibEntry; aesop;
    · simp_all +decide [ Finset.prod_eq_zero_iff ];
      simp_all +decide [ ← ih ];
      simp +decide [ fibEntry ];
    · rw [ ← ih, fibEntry_coprime_mul ];
      · rfl;
      · exact Nat.Coprime.prod_right fun j hj => h.1 j hj ( by aesop )
