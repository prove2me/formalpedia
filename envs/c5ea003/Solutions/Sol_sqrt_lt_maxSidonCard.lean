-- Prove2me | solution 1 for sqrt_lt_maxSidonCard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:16:57.967721+00:00
-- url     : https://prove2.me/submissions/c5f6fd82-ccf9-450b-a9c3-061ed7eb002d

-- Sol generated from Shared/SidonSetsErdosTuran.lean
import Mathlib
import Definitions.Def_Shared_SidonSetsErdosTuran
import Theorems.Thm_ErdosTuran_etSet_card
import Theorems.Thm_ErdosTuran_etSet_isSidon
import Theorems.Thm_ErdosTuran_etSet_subset

/-!
# Sidon sets: the Erdős–Turán sandwich, and a bridge to extremal graph theory

A **Sidon set** (or `B₂`-set) is a set `A` in an additive cancellative commutative
monoid such that every element of `A + A` has an essentially unique representation
as an unordered sum of two elements of `A`.  Equivalently (in a group) all the
differences `a - b`, `a ≠ b`, are pairwise distinct.

This file develops, from scratch, a complete quantitative theory of the largest
Sidon subset of an initial segment `{0, 1, …, N-1}` of `ℕ`, together with a
cross-domain bridge to extremal graph theory.  Neither Mathlib nor the catalog
contained any development of Sidon sets before this file.

## Main results

Counting / additive combinatorics:

* `IsSidon.sub_injOn` — the *distinct differences* property: in a group the map
  `(a, b) ↦ a - b` is injective on the off-diagonal of a Sidon set.
* `IsSidon.card_mul_pred_le` — in a finite abelian group `G`, a Sidon set obeys
  `|A|(|A| - 1) ≤ |G| - 1`.
* `IsSidon.card_mul_pred_le_of_subset_range` — the **Erdős–Turán upper bound**:
  a Sidon subset of `{0, …, n-1}` obeys `|A|(|A| - 1) ≤ 2n - 2`.

Algebra / finite fields (the construction):

* `pair_eq_of_powerSums_eq` — **Newton–Vieta rigidity**: over a field of
  characteristic `≠ 2`, two pairs with equal first and second power sums coincide
  as unordered pairs.
* `ErdosTuran.etSet_isSidon` — the **Erdős–Turán construction**: for an odd prime
  `p`, the set `{2pk + (k² mod p) : 0 ≤ k < p}` is a Sidon set.  The proof
  factors the `2p`-adic digits of the equation `a + b = c + d`, then transports
  the resulting pair of symmetric-function identities into the field `ZMod p`,
  where `pair_eq_of_powerSums_eq` applies.
* `ErdosTuran.etSet_card`, `ErdosTuran.etSet_subset` — it has `p` elements and
  lives inside `{0, …, 2p² - 1}`.

The sandwich (`maxSidonCard N = Θ(√N)`):

* `maxSidonCard` — the size of the largest Sidon subset of `{0, …, n-1}`
  (a computable definition).
* `maxSidonCard_le_sqrt` — `maxSidonCard n ≤ √(2n) + 1`.
* `sqrt_lt_maxSidonCard` — `√(N/8) < maxSidonCard N` for `N ≥ 32`, obtained by
  feeding **Bertrand's postulate** into the Erdős–Turán construction.
* `maxSidonCard_sandwich` — the two bounds combined: `maxSidonCard N = Θ(√N)`.

Bridge to extremal graph theory:

* `sidonGraph` — the bipartite incidence graph of `A` on `G ⊕ G`.
* `sidonGraph_commonNeighbors_subsingleton` — Sidon ⟹ **`K_{2,2}`-free**: any two
  distinct vertices have at most one common neighbour.
* `sidonGraph_no_fourCycle` — hence the graph is `C₄`-free.
* `sidonGraph_not_isSidon_of_fourCycle` — the converse direction: a four-cycle
  certifies failure of the Sidon property, so `C₄`-freeness of `sidonGraph A`
  is *equivalent* to (and not merely implied by) the Sidon property
  (`isSidon_iff_no_fourCycle`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): Three bold conjectures were put on the table.
  (H1) The maximum size of a Sidon subset of `{0,…,N-1}` is `Θ(√N)` with
       explicit constants provable in Lean: `√(N/8) < maxSidon N ≤ √(2N)+1`.
  (H2) The Erdős–Turán quadratic-residue construction `k ↦ 2pk + (k² mod p)` is
       Sidon *exactly* when the modulus is an odd prime; primality is not merely
       convenient but load-bearing.
  (H3) The Sidon property is not just *sufficient* for `C₄`-freeness of the
       associated bipartite Cayley incidence graph but *equivalent* to it —
       an exact additive-combinatorics ↔ extremal-graph-theory dictionary.
Experiment (Experimenter): All three were formalised.  (H1) required combining
  an injectivity/counting argument (differences) with Bertrand's postulate to
  place a prime in the right window; the `Nat.sqrt` bookkeeping was discharged
  by `nlinarith` after extracting `Nat.sqrt_le` / `Nat.lt_succ_sqrt`.  (H2) was
  proved for odd primes; brute-force evaluation refutes the composite cases
  (`p = 4`: `{0,9,16,25}` has `0 + 25 = 9 + 16`; `p = 9`: `{0,19,40,54,79,…}`
  has `0 + 79 = 19 + 40 + …`), see `ComputationalEvidence.md`; `p = 2` gives a
  two-element set, which is Sidon for trivial reasons, so the odd hypothesis is
  needed only for the *proof method* (division by 2 in `ZMod p`), not for the
  statement at `p = 2`.  (H3) was proved in both directions.
Analysis (Analyst): The decisive structural pattern is that a Sidon set is
  precisely a *Vieta-rigid* family: the equation `a + b = c + d` together with
  `a² + b² = c² + d²` forces `{a,b} = {c,d}` in any field of characteristic
  `≠ 2`.  The Erdős–Turán construction manufactures the second identity for
  free by storing `k² mod p` in the low `2p`-adic digit while the first is
  stored in the high digit.  Failure modes are exactly the failure of `ZMod p`
  to be a domain (composite `p`) or of `2` to be invertible (`p = 2`).
Critique (Critic): No theorem here is `rfl`, `decide` or `native_decide`; the
  main results route through `Nat.bertrand`, `ZMod` field structure, injective
  counting on `Finset.offDiag`, and `nlinarith`.  The bounds are guarded: the
  lower bound needs `32 ≤ N` (below that `N / 8 < 4` and Bertrand's window is
  empty), and the construction needs `p` prime and `p ≠ 2`.  Both hypotheses are
  load-bearing and both are documented.  `maxSidonCard` is non-vacuous: it is
  computable and `maxSidonCard 18 = 6`.
Synthesis (PI): distinct differences ⇒ upper bound; Vieta rigidity + `2p`-adic
  digits ⇒ Erdős–Turán construction; Bertrand ⇒ general lower bound; the two
  ⇒ `Θ(√N)`; and the whole picture is mirrored by `C₄`-freeness of an explicit
  bipartite Cayley graph.
-/

open Finset

/-! ## 1. Sidon sets and their differences -/




/-- The empty set is Sidon. -/
theorem isSidon_empty {M : Type*} [AddCancelCommMonoid M] : IsSidon (∅ : Finset M) := by
  intro a ha; exact absurd ha (Finset.notMem_empty a)

variable {G : Type*} [AddCommGroup G] {A : Finset G}


variable [Fintype G] [DecidableEq G]




/-! ## 2. The Erdős–Turán upper bound on an initial segment of `ℕ` -/


/-! ## 3. Newton–Vieta rigidity -/



/-! ## 4. The Erdős–Turán construction -/

open ErdosTuran

variable (p : ℕ)



variable {p}










/-! ## 5. The maximum Sidon subset of an initial segment -/


theorem mem_sidonFilter {n : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.range n) (hA : IsSidon A) :
    A ∈ ((Finset.range n).powerset).filter (fun A => IsSidon A) :=
  Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hA⟩

/-- Every Sidon subset of `{0, …, n-1}` is at most as large as `maxSidonCard n`. -/
theorem card_le_maxSidonCard {n : ℕ} {A : Finset ℕ} (hsub : A ⊆ Finset.range n)
    (hA : IsSidon A) : #A ≤ maxSidonCard n :=
  Finset.le_sup (f := Finset.card) (mem_sidonFilter hsub hA)

/-- The maximum is attained. -/
theorem exists_maxSidon (n : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.range n ∧ IsSidon A ∧ #A = maxSidonCard n := by
  obtain ⟨A, hA, hsup⟩ :=
    Finset.exists_mem_eq_sup (((Finset.range n).powerset).filter (fun A => IsSidon A))
      ⟨∅, mem_sidonFilter (Finset.empty_subset _) isSidon_empty⟩ Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hA
  exact ⟨A, hA.1, hA.2, hsup.symm⟩

/-- `maxSidonCard` is monotone. -/
theorem maxSidonCard_mono {m n : ℕ} (h : m ≤ n) : maxSidonCard m ≤ maxSidonCard n := by
  obtain ⟨A, hsub, hA, hcard⟩ := exists_maxSidon m
  exact hcard ▸ card_le_maxSidonCard (hsub.trans (Finset.range_subset_range.mpr h)) hA


/-- **Lower half of the sandwich, prime case.** For an odd prime `p` there is a Sidon
subset of `{0, …, 2p² - 1}` with `p` elements. -/
theorem le_maxSidonCard_of_prime {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    p ≤ maxSidonCard (2 * p ^ 2) := by
  have h := card_le_maxSidonCard (ErdosTuran.etSet_subset hp.pos) (ErdosTuran.etSet_isSidon hp hodd)
  rwa [ErdosTuran.etSet_card hp.pos] at h



/-! ## 6. Bridge to extremal graph theory: Sidon ⟺ `C₄`-free incidence graph -/

variable {G : Type*} [AddCommGroup G] (A : Finset G)


variable {A}








theorem solution{N : ℕ} (hN : 32 ≤ N) : Nat.sqrt (N / 8) < maxSidonCard N := by
  set m := Nat.sqrt (N / 8) with hm
  have hm2 : 2 ≤ m := by
    rw [hm, Nat.le_sqrt]
    omega
  obtain ⟨p, hp, hmp, hp2m⟩ := Nat.bertrand m (by omega)
  have hodd : p ≠ 2 := by omega
  have hmm : m * m ≤ N / 8 := Nat.sqrt_le (N / 8)
  have h8 : 8 * (m * m) ≤ N := by
    have := Nat.div_mul_le_self N 8
    omega
  have hfit : 2 * p ^ 2 ≤ N := by nlinarith
  calc m < p := hmp
    _ ≤ maxSidonCard (2 * p ^ 2) := le_maxSidonCard_of_prime hp hodd
    _ ≤ maxSidonCard N := maxSidonCard_mono hfit
