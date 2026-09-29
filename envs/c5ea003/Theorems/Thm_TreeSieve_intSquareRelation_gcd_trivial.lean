-- Prove2me | Theorems.Thm_TreeSieve_intSquareRelation_gcd_trivial
-- name    : TreeSieve.intSquareRelation_gcd_trivial
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:18:11.839887+00:00
-- url     : https://prove2.me/theorems/a73f10db-e367-4211-a098-e64582704460
-- title:
--   Obstruction 1.
-- statement:
--   **Obstruction 1.**  A square identity that holds *in `ℤ`* produces the
--   difference `0`, so the gcd step returns `N` itself: no split.
--
--   ```lean
--   theorem TreeSieve.intSquareRelation_gcd_trivial{X Y : ℤ} (N : ℤ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
--       (h : X ^ 2 = Y ^ 2) : Int.gcd (X - Y) N = N.natAbs := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TreeSieveLottery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TreeSieveLottery.lean#L57

-- Thm stub generated from Bridges/TreeSieveLottery.lean
import Mathlib
import Definitions.Def_Bridges_TreeSieveLottery

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

open TreeSieve

/-! ## Obstruction 1: integer identities are vacuous modulo `N` -/

theorem TreeSieve.intSquareRelation_gcd_trivial{X Y : ℤ} (N : ℤ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (h : X ^ 2 = Y ^ 2) : Int.gcd (X - Y) N = N.natAbs := by sorry
