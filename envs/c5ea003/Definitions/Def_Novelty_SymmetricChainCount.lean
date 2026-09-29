-- Prove2me | Definitions.Def_Novelty_SymmetricChainCount
-- name    : Novelty_SymmetricChainCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:42.08101+00:00
-- url     : https://prove2.me/theorems/0b6cb2ac-8452-435f-8a37-2fbf48ea57e1
-- title:
--   Aether Catalog definitions — Novelty_SymmetricChainCount
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SymmetricChainCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SymmetricChainCount.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_SuperExponential
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A super-exponential lower bound for symmetric chain decompositions

The paper's conjecture is that, for fixed `m > 1`, the number of *symmetric chain
decompositions* (SCDs) of the minuscule lattice `L(m,n)` — and, in the extension,
of the lattice `M(n)` of partitions into distinct parts `≤ n` — grows
super-exponentially in `n`.

The structural driver of super-exponential growth is the *middle of the poset*:
two consecutive rank levels of (nearly) equal, large size with a dense
comparability (Hasse) graph between them.  Restricted to such a slab, a symmetric
chain decomposition must pair up the two levels — i.e. it is a **perfect
matching** of a complete bipartite graph — and the number of perfect matchings of
`K_{n,n}` is `n!`, already super-exponential.

This file makes that mechanism rigorous on the cleanest possible carrier: the
**complete two-level poset** `CB n` with bottom level and top level each of size
`n` and every bottom element below every top element (Hasse graph `K_{n,n}`).  We
prove

* `factorial_le_numSCD` : `n! ≤ numSCD n`, the number of symmetric chain
  decompositions of `CB n`, via the injection `σ ↦ permChains σ` from the `n!`
  permutations of `Fin n`;
* `numSCD_superexp` : consequently `numSCD` grows super-exponentially.

This is an honest, fully-proved *lower-bound model* for the conjectured behaviour:
it isolates and verifies the matching mechanism that the conjecture attributes to
the middle ranks of `M(n)`.  (The faithful statement for `M(n)` itself remains a
conjecture; see `FUTURE_DIRECTIONS.md`.)

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer): the super-exponential blow-up in #SCD comes from
perfect matchings between two equal full levels; the count there is exactly `n!`.
EXPERIMENT (Experimenter): model the slab as `CB n = Bool × Fin n`; a symmetric
saturated chain is a pair `{(false,i),(true,j)}`; an SCD is a partition of the
carrier into such pairs.  Each permutation `σ` yields the SCD
`{ {(false,i),(true,σ i)} : i }`, and distinct `σ` give distinct SCDs.
ANALYSIS (Analyst): a full *bijection* SCD ↔ permutation would give equality
`numSCD n = n!`; we only need the *injection* (lower bound) for super-exponential
growth, which avoids the harder "recover the permutation from an abstract
partition" direction.  Recorded as a future direction.
CRITIQUE (Critic): is the bound vacuous?  No — `permChains` is a genuine injection
into the *filtered* set of partitions-into-symmetric-chains, and the target count
`numSCD` counts honest partitions, not permutations by fiat.
SYNTHESIS (PI): combine `factorial_le_numSCD` with `SuperExp.of_eventually_le`
(from `SuperExponential.lean`) and `factorial_superexp`.
-/

open Finset

namespace Novelty.SCD

/-- Carrier of the complete two-level poset: `false` marks the bottom level,
`true` the top level, each indexed by `Fin n`. -/
abbrev CB (n : ℕ) := Bool × Fin n

/-- A **symmetric saturated chain** in `CB n`: a two-element set consisting of one
bottom vertex `(false, i)` and one top vertex `(true, j)`. -/
def IsSymChain (n : ℕ) (c : Finset (CB n)) : Prop :=
  ∃ i j : Fin n, c = ({(false, i), (true, j)} : Finset (CB n))

/-- A **symmetric chain decomposition** of `CB n`: a finite family of symmetric
chains that partitions the carrier (pairwise disjoint, union everything, no empty
chain). -/
def IsSCD (n : ℕ) (P : Finset (Finset (CB n))) : Prop :=
  (∀ c ∈ P, IsSymChain n c) ∧ (↑P : Set (Finset (CB n))).PairwiseDisjoint id ∧
    P.sup id = Finset.univ ∧ ∅ ∉ P

open Classical in
/-- The number of symmetric chain decompositions of `CB n`. -/
noncomputable def numSCD (n : ℕ) : ℕ :=
  (Finset.univ.filter (IsSCD n)).card

/-- The symmetric chain decomposition associated to a permutation `σ`: pair each
bottom vertex `(false, i)` with the top vertex `(true, σ i)`. -/
def permChains (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset (Finset (CB n)) :=
  Finset.univ.image (fun i : Fin n => ({(false, i), (true, σ i)} : Finset (CB n)))

/-
A chain pair `{(false,i),(true,j)}` has exactly two elements.
-/

/-
`permChains σ` is a genuine symmetric chain decomposition of `CB n`.
-/

/-
Distinct permutations give distinct symmetric chain decompositions.
-/



end Novelty.SCD


