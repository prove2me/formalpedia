-- Prove2me | solution 1 for Hashimoto.rowSum_hashimoto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:43:03.916009+00:00
-- url     : https://prove2.me/submissions/dc01164e-b3a4-4bf5-893c-aa6364b72ebf

-- Sol generated from Algebra/NonBacktracking/HashimotoTrace.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount

/-!
# `trace (Bⁿ)` counts rooted closed non-backtracking walks of length `n`

Let `G` be a finite simple graph and let `B` be its **Hashimoto (non-backtracking)
matrix**: the `0-1` matrix indexed by the *darts* (oriented edges) of `G` with

`B d d' = 1` iff `d` and `d'` are composable (`d.snd = d'.fst`) and `d'` is not the
reversal of `d`.

The main results of this file are the two forms of the trace formula:

* `Hashimoto.trace_hashimoto_pow` :
  `trace (B ^ n) = #{ rooted closed non-backtracking walks of length n }`,
  where such a walk is a list of `n + 1` darts, consecutive darts composable without
  backtracking, whose first and last dart agree (the root);
* `Hashimoto.trace_hashimoto_pow_eq_card_nbCycles` (for `1 ≤ n`) :
  `trace (B ^ n) = #{ cyclically non-backtracking sequences of n darts }`,
  the classical "rooted closed non-backtracking walk of length `n`" of Ihara-zeta
  theory: `n` darts arranged in a cycle, non-backtracking also across the seam.

Both counts are genuine finite cardinalities (`Finset.card`), and the two counting
sets are proved to be in bijection (`Hashimoto.card_nbCycles`).

We also prove the first structural consequences:

* `Hashimoto.trace_hashimoto_pow_zero` : `trace (B ^ 0) = #darts = ∑ v, deg v`;
* `Hashimoto.trace_hashimoto` and `Hashimoto.trace_hashimoto_sq` : `trace B = trace (B²) = 0`
  (a graph has no closed non-backtracking walks of length `1` or `2`);
* `Hashimoto.rowSum_hashimoto` : the `d`-th row of `B` sums to `deg (d.snd) - 1`;
* `Hashimoto.trace_hashimoto_pow_le_of_regular` : for a `(q+1)`-regular graph,
  `trace (B ^ n) ≤ (#darts) * qⁿ`, i.e. the exponential growth rate of the number of
  closed non-backtracking walks is at most `q` (the Ihara/Alon–Boppana regime).

The underlying general digraph walk-counting machinery lives in
`Algebra.NonBacktracking.RelWalkCount`.
-/

open Finset RelWalkCount SimpleGraph

open Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


/-! ## The non-backtracking relation on darts -/



variable {G}




variable (G)

/-! ## The Hashimoto matrix -/



/-! ## Rooted closed non-backtracking walks -/





/-! ## The cyclic description -/


variable {G}





variable (G)


/-! ## First consequences -/






/-! ## Length three: closed non-backtracking walks are oriented triangles -/


variable {G}



variable (G)


/-! ## Row sums and the Ihara growth bound -/





open Hashimoto in
theorem solution(d : G.Dart) :
    ∑ d' : G.Dart, hashimoto G d d' = G.degree d.snd - 1 := by
  have hcard : ∑ d' : G.Dart, hashimoto G d d'
      = (Finset.univ.filter fun d' : G.Dart => NBAdj G d d').card := by
    rw [Finset.card_filter]
    rfl
  rw [hcard]
  have hbij : (Finset.univ.filter fun d' : G.Dart => NBAdj G d d').card
      = ((G.neighborFinset d.snd).erase d.fst).card := by
    refine Finset.card_bij (fun d' _ => d'.snd) ?_ ?_ ?_
    · intro d' hd'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
      obtain ⟨h1, h2⟩ := hd'
      refine Finset.mem_erase.2 ⟨h2, ?_⟩
      rw [SimpleGraph.mem_neighborFinset, h1]
      exact d'.adj
    · intro d₁ h₁ d₂ h₂ hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      exact SimpleGraph.Dart.ext _ _ (Prod.ext (h₁.1 ▸ h₂.1 ▸ rfl) hEq)
    · intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_erase.1 hw
      rw [SimpleGraph.mem_neighborFinset] at hw2
      refine ⟨⟨(d.snd, w), hw2⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨rfl, hw1⟩
  rw [hbij, Finset.card_erase_of_mem, SimpleGraph.card_neighborFinset_eq_degree]
  rw [SimpleGraph.mem_neighborFinset]
  exact d.adj.symm
