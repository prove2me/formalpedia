-- Prove2me | solution 1 for TreeSieve.dixon_split_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:09.580857+00:00
-- url     : https://prove2.me/submissions/ba560f46-035f-4a23-a60f-a027a376fb6b

-- Sol generated from Bridges/TreeSieveLottery.lean
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




/-! ## The corrected mechanism: Dixon's congruence of squares -/


/-! ## Obstruction 2: the lottery bound for `N`-independent tickets -/





/-! ## Obstruction 3: BFS starvation in the Berggren tree -/



















open TreeSieve in
theorem solution{N x y : ℤ} (hN : 1 < N) (hdvd : N ∣ (x - y) * (x + y))
    (h1 : ¬ N ∣ (x - y)) (h2 : ¬ N ∣ (x + y)) :
    1 < Int.gcd (x - y) N ∧ (Int.gcd (x - y) N : ℤ) < N := by
  have hgdvd : (Int.gcd (x - y) N : ℤ) ∣ N := Int.gcd_dvd_right _ _
  constructor
  · by_contra hle
    push_neg at hle
    interval_cases hg : Int.gcd (x - y) N
    · exact h1 ((Int.gcd_eq_zero_iff.mp hg).1 ▸ dvd_zero N)
    · have hcop : IsCoprime (x - y) N := Int.isCoprime_iff_gcd_eq_one.mpr hg
      exact h2 (hcop.symm.dvd_of_dvd_mul_left hdvd)
  · rcases lt_or_eq_of_le (Int.le_of_dvd (by omega) hgdvd) with h | h
    · exact h
    · exact absurd (h ▸ Int.gcd_dvd_left (a := x - y) (b := N)) h1
