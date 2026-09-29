-- Prove2me | solution 1 for Hashimoto.exists_walk_of_dartChain
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:05:10.591984+00:00
-- url     : https://prove2.me/submissions/2462806a-d642-4f99-bcc4-d9b3ec6e5fe2

-- Sol generated from Algebra/NonBacktracking/AcyclicVanishing.lean
import Mathlib

/-!
# Forests have identically vanishing non-backtracking trace

`Algebra.NonBacktracking.CyclePositivity` shows that a cycle in `G` forces some positive
power of the Hashimoto matrix to have positive trace. Here we prove the converse
implication, completing the characterisation

`G.IsAcyclic ↔ ∀ n ≥ 1, trace (B ^ n) = 0`.

The mathematical content is that a *closed* non-backtracking walk cannot exist in a
forest. The proof turns a cyclic list of darts into an honest `SimpleGraph.Walk`; the
non-backtracking condition says exactly that consecutive edges of that walk differ, and
in an acyclic graph such a walk is a path (`SimpleGraph.IsAcyclic.isPath_iff_isChain`).
A closed path is trivial, so the walk has length `0`, contradicting `n ≥ 1`.

## Main results

* `Hashimoto.exists_walk_of_dartChain` — a composable list of darts is the dart list of a
  walk (the inverse construction to `SimpleGraph.Walk.darts`);
* `Hashimoto.isChain_ne_edges_of_isChain_nbAdj` — non-backtracking dart chains have
  chains of pairwise-consecutively-distinct edges;
* `Hashimoto.trace_hashimoto_pow_eq_zero_of_isAcyclic` — forests kill all positive
  powers of `B`;
* `Hashimoto.isAcyclic_iff_trace_hashimoto_pow_eq_zero` — the resulting characterisation;
* `Hashimoto.closedNBWalks_eq_empty_of_isAcyclic` — the combinatorial form: a forest has
  no rooted closed non-backtracking walk of positive length.
-/

open Finset SimpleGraph List


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Reconstructing a walk from its darts -/


/-! ## Non-backtracking means consecutive edges differ -/



/-! ## Vanishing of the trace on forests -/






omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem solution:
    ∀ (c : List G.Dart) (a b : V),
      List.IsChain (fun d d' : G.Dart => d.toProd.2 = d'.toProd.1) c →
      (∀ d ∈ c.head?, d.toProd.1 = a) →
      (∀ d ∈ c.getLast?, d.toProd.2 = b) →
      (c = [] → a = b) →
      ∃ p : G.Walk a b, p.darts = c := by
  intro c
  induction c with
  | nil =>
      intro a b _ _ _ hab
      obtain rfl := hab rfl
      exact ⟨Walk.nil, rfl⟩
  | cons d t ih =>
      intro a b hchain hhead hlast _
      have ha : d.toProd.1 = a := hhead d (by simp)
      subst ha
      rw [List.isChain_cons] at hchain
      cases t with
      | nil =>
          have hb : d.toProd.2 = b := hlast d (by simp)
          subst hb
          exact ⟨Walk.cons d.adj Walk.nil, by simp⟩
      | cons d' t' =>
          have hcomp : d.toProd.2 = d'.toProd.1 := hchain.1 d' (by simp)
          obtain ⟨p, hp⟩ := ih d.toProd.2 b hchain.2
            (by intro x hx; simp only [List.head?_cons, Option.mem_def,
                  Option.some.injEq] at hx; subst hx; exact hcomp.symm)
            (by
              intro x hx
              refine hlast x ?_
              rwa [List.getLast?_cons_cons])
            (by simp)
          exact ⟨Walk.cons d.adj p, by simp [hp]⟩
