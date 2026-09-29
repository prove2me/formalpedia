-- Prove2me | Definitions.Def_Algebra_NonBacktracking_HashimotoTrace
-- name    : Algebra_NonBacktracking_HashimotoTrace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:23:41.577757+00:00
-- url     : https://prove2.me/theorems/5c022a80-497f-487a-b34a-93e138039a70
-- title:
--   Aether Catalog definitions — Algebra_NonBacktracking_HashimotoTrace
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.NonBacktracking.HashimotoTrace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/NonBacktracking/HashimotoTrace.lean by skeleton subtraction
import Mathlib
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

namespace Hashimoto

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

instance : DecidableEq G.Dart := fun d d' =>
  decidable_of_iff _ (SimpleGraph.Dart.ext_iff d d').symm

/-! ## The non-backtracking relation on darts -/

/-- Two darts are **non-backtracking adjacent** when the head of the first is the tail of
the second and the second is not the reversal of the first. -/
def NBAdj (d d' : G.Dart) : Prop := d.snd = d'.fst ∧ d'.snd ≠ d.fst

instance : DecidableRel (NBAdj G) := fun d d' => by unfold NBAdj; infer_instance

variable {G}




variable (G)

/-! ## The Hashimoto matrix -/

/-- The **Hashimoto (non-backtracking) matrix** of a finite simple graph: the `0-1`
matrix indexed by darts of the non-backtracking adjacency relation. -/
def hashimoto : Matrix G.Dart G.Dart ℕ := relMatrix (NBAdj G)


/-! ## Rooted closed non-backtracking walks -/

/-- A **rooted closed non-backtracking walk of length `n`** in `G`: a list of `n + 1`
darts, consecutive darts non-backtracking adjacent, whose first and last dart agree.
The first dart is the root. -/
def IsClosedNBWalk (n : ℕ) (l : List G.Dart) : Prop :=
  l.length = n + 1 ∧ List.IsChain (NBAdj G) l ∧ l.head? = l.getLast?

/-- The finset of rooted closed non-backtracking walks of length `n`. -/
def closedNBWalks (n : ℕ) : Finset (List G.Dart) := closedWalks (NBAdj G) n



/-! ## The cyclic description -/

/-- The finset of **cyclically non-backtracking closed sequences of `n` darts**, obtained
from rooted closed non-backtracking walks by deleting the repeated final dart. -/
def nbCycles (n : ℕ) : Finset (List G.Dart) := (closedNBWalks G n).image List.dropLast

variable {G}





variable (G)


/-! ## First consequences -/






/-! ## Length three: closed non-backtracking walks are oriented triangles -/

/-- Ordered triangles of `G`: triples of vertices that are cyclically adjacent.
Adjacency forces the three vertices to be pairwise distinct, so each (unordered)
triangle of `G` is counted `6` times. -/
def orderedTriangles : Finset (V × V × V) :=
  Finset.univ.filter fun t => G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1

variable {G}


/-- The three darts running around an ordered triangle. -/
def triDarts (t : V × V × V)
    (h : G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1) : List G.Dart :=
  [⟨(t.1, t.2.1), h.1⟩, ⟨(t.2.1, t.2.2), h.2.1⟩, ⟨(t.2.2, t.1), h.2.2⟩]

variable (G)


/-! ## Row sums and the Ihara growth bound -/




end Hashimoto


