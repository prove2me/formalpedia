-- Prove2me | solution 1 for SymmetryBreakingCost.QTree.exists_solving_tree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:01:19.673985+00:00
-- url     : https://prove2.me/submissions/517eb1b7-e32a-44aa-aaee-83be63f4f26f

-- Sol generated from Novelty/SymmetryBreakingCostAdaptive.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostAdaptive
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Theorems.Thm_SymmetryBreakingCost_exists_isolating_battery
import Theorems.Thm_SymmetryBreakingCost_qsig_eq_of_bits

/-!
# Adaptivity buys nothing: the isolation cost is a decision-tree invariant

The first cycle measured the isolation cost of a *non-adaptive* battery: a fixed tuple of test
integers, all queries chosen in advance.  A natural objection is that an adaptive strategy —
choosing the next test integer after seeing the previous answers — could be cheaper.  It is not.

We model an adaptive strategy as a binary decision tree `QTree`: each internal node carries a
test integer `x`, and the candidate `r` is routed left when `J(x | r) = 1` and right otherwise;
each leaf outputs a guess.  A tree *solves* a candidate set `S` when it outputs `r` on every
`r ∈ S`.

* `QTree.card_le_two_pow_depth` : a tree of depth `d` solves at most `2 ^ d` candidates.
* `QTree.clog_le_depth` : hence every adaptive strategy needs depth at least `⌈log₂ |S|⌉`.
* `QTree.exists_solving_tree` : and `⌈log₂ |S|⌉` is achieved, by the *non-adaptive* battery of
  the first cycle compiled into a complete binary tree.
* `adaptiveCost_isLeast` : the least depth of a solving tree is exactly `Nat.clog 2 S.card`,
  the same number as the non-adaptive cost `isolationCost_isLeast`.

So the `⌈log₂ π(√N)⌉` figure is not an artefact of the non-adaptive model: it is the exact
query complexity of the residue oracle, adaptively or not.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 3): adaptivity can only help when answers are *unbalanced*; here
the Chinese remainder theorem makes every answer pattern realisable, so the tree is forced to be
complete and adaptivity gains nothing.

Experiment (Experimenter): exhaustive search over all decision trees of depth `≤ 3` on the
candidate set `{3, 5, 7, 11, 13}` (`|S| = 5`, `⌈log₂ 5⌉ = 3`): no tree of depth `2` separates
the five candidates (each such tree has at most `4` leaves), while the battery `[2, 3, 10]`
compiled into a complete tree of depth `3` does — its answer patterns on `3, 5, 7, 11, 13` are
`(-1,0,1), (-1,-1,0), (1,-1,-1), (-1,1,-1), (-1,1,1)`, pairwise distinct.

Analysis (Analyst): the lower bound is a pure counting induction on the tree — the candidate set
splits into the two subtrees, and `2 ^ a + 2 ^ b ≤ 2 ^ (max a b + 1)`.  The upper bound reuses
the CRT construction verbatim, showing that the two bounds meet.

Critique (Critic): the model must allow *arbitrary* integers at each node, otherwise the lower
bound would be about a restricted strategy class; `QTree.node` carries an unrestricted `ℤ`, and
the routing predicate is the raw Jacobi answer, so no strategy is excluded.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols


open QTree








theorem depth_full : ∀ (xs : List ℤ) (dec : List Bool → ℕ), (full xs dec).depth = xs.length
  | [], dec => by simp [full, depth]
  | x :: xs, dec => by
      simp [full, depth, depth_full xs]

theorem run_full : ∀ (xs : List ℤ) (dec : List Bool → ℕ) (r : ℕ),
    (full xs dec).run r = dec (sigList xs r)
  | [], dec, r => by simp [full, run, sigList]
  | x :: xs, dec, r => by
      by_cases hx : J(x | r) = 1
      · simp [full, run, sigList, hx, run_full xs]
      · simp [full, run, sigList, hx, run_full xs]





open SymmetryBreakingCost in
theorem solution(S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    ∃ t : QTree, t.depth = Nat.clog 2 S.card ∧ t.Solves S := by
  classical
  set k : ℕ := Nat.clog 2 S.card with hk
  obtain ⟨a, hadm, hiso⟩ := exists_isolating_battery S hS (Nat.le_pow_clog (by norm_num) _)
  set xs : List ℤ := List.ofFn a with hxs
  have hsig : ∀ r : ℕ, sigList xs r = List.ofFn (fun i => decide (J(a i | r) = 1)) := by
    intro r
    simp [sigList, hxs, List.map_ofFn]
    rfl
  have hinj : ∀ p ∈ S, ∀ q ∈ S, sigList xs p = sigList xs q → p = q := by
    intro p hp q hq hpq
    rw [hsig, hsig] at hpq
    have hfun := List.ofFn_inj.mp hpq
    refine hiso hp hq (qsig_eq_of_bits hadm hp hq (fun i => ?_))
    have := congrFun hfun i
    simpa using this
  set dec : List Bool → ℕ := fun bs =>
    if h : ∃ r, r ∈ S ∧ sigList xs r = bs then h.choose else 0 with hdec
  refine ⟨full xs dec, ?_, ?_⟩
  · rw [depth_full, hxs, List.length_ofFn]
  · intro r hr
    rw [run_full]
    have hex : ∃ s, s ∈ S ∧ sigList xs s = sigList xs r := ⟨r, hr, rfl⟩
    simp only [hdec, dif_pos hex]
    obtain ⟨hmem, heq⟩ := hex.choose_spec
    exact hinj _ hmem _ hr heq
