-- Prove2me | solution 1 for TreeSieve.bergFrom_hyp_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:01:09.101038+00:00
-- url     : https://prove2.me/submissions/ebab4c76-b206-4005-a0cf-2b4290eba0d1

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







theorem adm_step (i : Fin 3) {t : Triple} (h : Adm t) : Adm (step i t) := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [Adm] at *
  fin_cases i <;> simp only [step] <;> refine ⟨by omega, by omega, by omega, by omega⟩





/-- One Berggren move multiplies the hypotenuse by at most `7`. -/
theorem step_hyp_le (i : Fin 3) {t : Triple} (h : Adm t) :
    (step i t).2.2 ≤ 7 * t.2.2 := by
  obtain ⟨a, b, c⟩ := t
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at *
  fin_cases i <;> simp only [step] <;> omega







open TreeSieve in
theorem solution(w : List (Fin 3)) {t : Triple} (h : Adm t) :
    (bergFrom t w).2.2 ≤ 7 ^ w.length * t.2.2 := by
  induction w generalizing t with
  | nil => simp [bergFrom]
  | cons i w ih =>
      have hstep := ih (adm_step i h)
      have h7 := step_hyp_le i h
      have hpos : (0:ℤ) < 7 ^ w.length := by positivity
      calc (bergFrom t (i :: w)).2.2 = (bergFrom (step i t) w).2.2 := rfl
        _ ≤ 7 ^ w.length * (step i t).2.2 := hstep
        _ ≤ 7 ^ w.length * (7 * t.2.2) := by
              exact mul_le_mul_of_nonneg_left h7 (le_of_lt hpos)
        _ = 7 ^ (i :: w).length * t.2.2 := by simp [List.length_cons, pow_succ]; ring
