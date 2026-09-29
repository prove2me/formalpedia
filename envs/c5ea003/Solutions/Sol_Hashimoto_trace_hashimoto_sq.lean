-- Prove2me | solution 1 for Hashimoto.trace_hashimoto_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:12:29.705068+00:00
-- url     : https://prove2.me/submissions/2793a9a7-3c48-4b6c-a710-5a87dd3de5a8

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



omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- There are no non-backtracking `2`-cycles of darts. -/
lemma not_nbAdj_symm {d d' : G.Dart} (h : NBAdj G d d') : ¬ NBAdj G d' d := by
  rintro ⟨h1, h2⟩
  exact h.2 h1

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
theorem solution: (hashimoto G ^ 2).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun d _ => ?_
  simp only [Matrix.diag, pow_two, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun d' _ => ?_
  simp only [hashimoto, relMatrix, Matrix.of_apply]
  by_cases h : NBAdj G d d'
  · simp [if_neg (not_nbAdj_symm h)]
  · simp [if_neg h]
