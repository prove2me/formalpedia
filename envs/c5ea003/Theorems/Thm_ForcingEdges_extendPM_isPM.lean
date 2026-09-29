-- Prove2me | Theorems.Thm_ForcingEdges_extendPM_isPM
-- name    : ForcingEdges.extendPM_isPM
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:35.526596+00:00
-- url     : https://prove2.me/theorems/0c0053c7-2b07-4f71-851b-b70e01aef13c
-- title:
--   ExtendPM isPM
-- statement:
--   Formal statement of `ForcingEdges.extendPM_isPM` from the Aether Catalog (Speculative). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ForcingEdges.extendPM_isPM[DecidableEq V] {G : SimpleGraph V} {u v : V} {h : V → V}
--       (hh : IsPMdel G u v h) (hadj : G.Adj u v) :
--       IsPM G (extendPM u v h) ∧ extendPM u v h u = v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/Basic.lean#L110

-- Thm stub generated from Speculative/NumberTheory/Basic.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_Basic

/-!
# Forcing edges of perfect matchings, via fixed-point-free involutions

This file develops a small, self-contained theory of **forcing edges** of perfect
matchings, motivated by the structural theory of *bricks* and *b-invariant edges*
in matching theory (de Carvalho–Lucchesi–Murty; Lovász).  An edge `e` of a graph
`G` is a **forcing edge** if there is exactly one perfect matching of `G` that
contains `e`.  Equivalently, `e = uv` is forcing precisely when the graph obtained
by deleting `u` and `v` has a *unique* perfect matching — this is the classical
deletion characterisation, and it is our main theorem (`forcing_iff_unique_deletion`).

## Model

A perfect matching of a simple graph `G` is modelled as a **fixed-point-free
involution** `f : V → V` all of whose swapped pairs `{v, f v}` are edges of `G`
(`IsPM`).  This turns "the perfect matching containing `uv`" into "the involution
`f` with `f u = v`", which is very convenient for reasoning about uniqueness.

Deleting the two endpoints `u, v` of an edge is modelled by `IsPMdel`: an
involution that fixes exactly `u` and `v` and matches every other vertex to a
neighbour distinct from `u, v`.

## Main results

* `IsPM.apply_ne` — matched partners of interior vertices avoid `u, v`.
* `restrictPM_isPMdel` / `extendPM_isPM` — the deletion bijection.
* `uniquePM_all_forcing` — if `G` has a unique perfect matching, every one of its
  edges is forcing.
* `forcing_iff_unique_deletion` — **main theorem**: `uv` is forcing iff `uv` is an
  edge and `G - u - v` has a unique perfect matching.
* `forcing_comm` — forcing is a symmetric relation on the endpoints.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The property "`uv` lies in a unique perfect matching"
should be *local*: it should depend only on the perfect matchings of the graph
with `u, v` deleted. Concretely, deleting the endpoints of a forcing edge must
leave a graph with a unique perfect matching, and conversely.

Experiment (Experimenter): Modelling perfect matchings as fixed-point-free
involutions makes "the matching containing `uv`" literally the constraint
`f u = v`. The map `f ↦ (f restricted to V \ {u,v})` and its inverse `extend`
form a bijection between {perfect matchings with `f u = v`} and {perfect matchings
of the deleted graph}. We verified the bijection laws on paper for the swap/fix
pattern before formalising.

Analysis (Analyst): The only non-trivial input is that in any perfect matching
containing `uv`, no interior vertex is matched to `u` or `v` (`IsPM.apply_ne`);
this is exactly injectivity of the involution. Everything else is bookkeeping of
the if-then-else definitions of `restrict`/`extend`.

Critique (Critic): The `u ≠ v` side condition is essential; it is supplied for
free by `G.Adj u v` (loopless graphs). The theorem is non-vacuous: `uniquePM`
graphs (e.g. a single edge, or a path) exhibit genuine forcing edges.

Synthesis (PI): The deletion characterisation is the engine behind the paper's
analysis of which b-invariant edges are forcing; here it is captured cleanly and
proved in full generality (no finiteness assumption).
-- !-- Lab Notes -- !--
-/

open ForcingEdges

open Function

variable {V : Type*}




/-
In a perfect matching containing the edge `uv`, no interior vertex is matched
to `u` or to `v`.
-/

theorem ForcingEdges.extendPM_isPM[DecidableEq V] {G : SimpleGraph V} {u v : V} {h : V → V}
    (hh : IsPMdel G u v h) (hadj : G.Adj u v) :
    IsPM G (extendPM u v h) ∧ extendPM u v h u = v := by sorry
