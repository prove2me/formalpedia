-- Prove2me | Definitions.Def_Bridges_TreeSieveLottery
-- name    : Bridges_TreeSieveLottery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:29:31.576912+00:00
-- url     : https://prove2.me/theorems/4b9ec906-9c1e-40f8-b10c-b6bdc73a95d9
-- title:
--   Aether Catalog definitions — Bridges_TreeSieveLottery
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TreeSieveLottery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TreeSieveLottery.lean by skeleton subtraction
import Mathlib

/-!
# The tree sieve is a lottery: three obstructions to Berggren-tree factoring

This file formalises the negative analysis of the "TREE-SIEVE" proposal
(round-72 experiment `exp556`): one collects leg pairs `(mᵢ, nᵢ)` from the
Berggren ternary tree of primitive Pythagorean triples, arranges that

  `∏ (mᵢ - nᵢ)(mᵢ + nᵢ) = Y²`

is a perfect square, and hopes that `gcd(X - Y, N)` splits a semiprime `N`.

Three independent obstructions are proved here.

## Obstruction 1 — an identity in `ℤ` carries no information mod `N`

`intSquareRelation_gcd_trivial`: if `X² = Y²` holds *in `ℤ`* with `X, Y ≥ 0`,
then `X = Y`, so `gcd (X - Y) N = N`: the returned "factor" is `N` itself.
A congruence of squares is only useful when it holds modulo `N` **and** the
two roots are inequivalent (`dixon_split_nontrivial` below).

## Obstruction 2 — `N`-independent tickets are a lottery

The candidate pairs produced by the tree do not depend on `N`, so the sieve
outputs a fixed integer `D` (`= X - Y`) and wins exactly when a prime factor of
`N` happens to divide `D`.  Since `D` has at most `log₂ D` prime factors, the
number of winning primes in any pool `S` of candidate primes is at most
`log₂ D` (`prime_hits_le_log`), and `k` tickets win on at most `∑ log₂ Dᵢ`
primes (`lottery_union_bound`) — tickets add linearly, exactly the behaviour
observed end-to-end (8/12000 versus 4/12000).  In probability form this is
`lottery_probability_bound`.

## Obstruction 3 — BFS starvation in the Berggren tree

Along every branch of the Berggren tree the hypotenuse grows by a factor of at
most `7`, so a node at depth `L` has hypotenuse at most `5 · 7 ^ L`
(`berg_hyp_le`).  Breadth-first search must expand at least `3 ^ L` nodes to
reach depth `L` (`three_pow_le_nodesUpTo`), and since `7 ≤ 9 = 3²` the number of
expanded nodes is at least the square root of the hypotenuse window:
`bfs_starvation` states `V ≤ 5 * (nodesUpTo L)²` whenever a node of depth `L`
has hypotenuse at least `V`.

Finally `dixon_split_nontrivial` shows that the *corrected* variant — forcing
`u ≡ v [ZMOD N]`-style congruences — is precisely the Dixon / quadratic-sieve
mechanism, which is where all corrected variants collapse.
-/

namespace TreeSieve

/-! ## Obstruction 1: integer identities are vacuous modulo `N` -/




/-! ## The corrected mechanism: Dixon's congruence of squares -/


/-! ## Obstruction 2: the lottery bound for `N`-independent tickets -/





/-! ## Obstruction 3: BFS starvation in the Berggren tree -/

/-- A Pythagorean triple, as a triple of integers. -/
abbrev Triple := ℤ × ℤ × ℤ

/-- The three Berggren transformations, indexed by `Fin 3`. -/
def step : Fin 3 → Triple → Triple
  | 0, (a, b, c) => (a - 2 * b + 2 * c, 2 * a - b + 2 * c, 2 * a - 2 * b + 3 * c)
  | 1, (a, b, c) => (a + 2 * b + 2 * c, 2 * a + b + 2 * c, 2 * a + 2 * b + 3 * c)
  | _, (a, b, c) => (-a + 2 * b + 2 * c, -2 * a + b + 2 * c, -2 * a + 2 * b + 3 * c)

/-- Following a word of moves from a given triple. -/
def bergFrom (t : Triple) : List (Fin 3) → Triple
  | [] => t
  | i :: w => bergFrom (step i t) w

/-- The node of the Berggren tree addressed by a word, rooted at `(3, 4, 5)`. -/
def bergOf (w : List (Fin 3)) : Triple := bergFrom (3, 4, 5) w

/-- The structural invariant of the tree: legs are positive and smaller than the
hypotenuse. -/
def Adm (t : Triple) : Prop := 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 < t.2.2 ∧ t.2.1 < t.2.2










/-- Number of nodes of depth at most `L` in a ternary tree. -/
def nodesUpTo (L : ℕ) : ℕ := ∑ i ∈ Finset.range (L + 1), 3 ^ i



end TreeSieve


