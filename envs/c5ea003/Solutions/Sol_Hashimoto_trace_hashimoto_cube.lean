-- Prove2me | solution 1 for Hashimoto.trace_hashimoto_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:45:03.518548+00:00
-- url     : https://prove2.me/submissions/0dcda812-2a6c-4af2-8555-588b8a416e1a

-- Sol generated from Algebra/NonBacktracking/HashimotoTrace.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount
import Theorems.Thm_Hashimoto_mem_nbCycles
import Theorems.Thm_Hashimoto_trace_hashimoto_pow_eq_card_nbCycles

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

omit [DecidableEq V] in
@[simp] lemma mem_orderedTriangles {t : V × V × V} :
    t ∈ orderedTriangles G ↔ G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1 := by
  simp [orderedTriangles]


variable (G)


/-! ## Row sums and the Ihara growth bound -/





open Hashimoto in
theorem solution:
    (hashimoto G ^ 3).trace = (orderedTriangles G).card := by
  rw [trace_hashimoto_pow_eq_card_nbCycles G (by norm_num)]
  refine (Finset.card_bij (fun t ht => triDarts t (mem_orderedTriangles.1 ht)) ?_ ?_ ?_).symm
  · intro t ht
    have hadj := mem_orderedTriangles.1 ht
    rw [mem_nbCycles (by norm_num : (1:ℕ) ≤ 3)]
    refine ⟨by simp [triDarts], ?_, ?_⟩
    · simp only [triDarts, List.isChain_cons_cons, List.IsChain.singleton, and_true]
      exact ⟨⟨rfl, by simpa using hadj.2.2.ne⟩, ⟨rfl, by simpa using hadj.1.ne⟩⟩
    · intro x hx y hy
      simp only [triDarts, List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
        Option.some.injEq] at hx
      simp only [triDarts, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hx; subst hy
      exact ⟨rfl, by simpa using hadj.2.1.ne⟩
  · intro t₁ h₁ t₂ h₂ hEq
    simp only [triDarts, List.cons.injEq, and_true] at hEq
    obtain ⟨e1, e2, -⟩ := hEq
    have q1 : ((t₁.1, t₁.2.1) : V × V) = (t₂.1, t₂.2.1) :=
      congrArg SimpleGraph.Dart.toProd e1
    have q2 : ((t₁.2.1, t₁.2.2) : V × V) = (t₂.2.1, t₂.2.2) :=
      congrArg SimpleGraph.Dart.toProd e2
    simp only [Prod.mk.injEq] at q1 q2
    exact Prod.ext q1.1 (Prod.ext q1.2 q2.2)
  · intro c hc
    rw [mem_nbCycles (by norm_num : (1:ℕ) ≤ 3)] at hc
    obtain ⟨hlen, hchain, hseam⟩ := hc
    match c, hlen with
    | [d0, d1, d2], _ =>
      simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true] at hchain
      have hs : NBAdj G d2 d0 := hseam d2 (by simp) d0 (by simp)
      have hadj : G.Adj d0.fst d1.fst ∧ G.Adj d1.fst d2.fst ∧ G.Adj d2.fst d0.fst := by
        refine ⟨?_, ?_, ?_⟩
        · rw [← hchain.1.1]; exact d0.adj
        · rw [← hchain.2.1]; exact d1.adj
        · rw [← hs.1]; exact d2.adj
      refine ⟨(d0.fst, d1.fst, d2.fst), mem_orderedTriangles.2 hadj, ?_⟩
      show triDarts (d0.fst, d1.fst, d2.fst) _ = _
      simp only [triDarts, List.cons.injEq, and_true]
      refine ⟨SimpleGraph.Dart.ext _ _ (Prod.ext rfl hchain.1.1.symm), ?_, ?_⟩
      · exact SimpleGraph.Dart.ext _ _ (Prod.ext rfl hchain.2.1.symm)
      · exact SimpleGraph.Dart.ext _ _ (Prod.ext rfl hs.1.symm)
