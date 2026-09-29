-- Prove2me | Definitions.Def_Speculative_NumberTheory_Basic
-- name    : Speculative_NumberTheory_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:42.954613+00:00
-- url     : https://prove2.me/theorems/ec9b53be-79bd-4fe1-95b3-b630dc69be7b
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/Basic.lean by skeleton subtraction
import Mathlib

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

namespace ForcingEdges

open Function

variable {V : Type*}

/-- `f` is a perfect matching of `G`: a fixed-point-free involution whose swapped
pairs are edges of `G`. -/
def IsPM (G : SimpleGraph V) (f : V → V) : Prop :=
  Involutive f ∧ (∀ v, f v ≠ v) ∧ (∀ v, G.Adj v (f v))

/-- The edge `uv` is a **forcing edge**: it is an edge, and there is exactly one
perfect matching of `G` containing it (i.e. one involution `f` with `f u = v`). -/
def Forcing (G : SimpleGraph V) (u v : V) : Prop :=
  G.Adj u v ∧ ∃! f, IsPM G f ∧ f u = v

/-- `h` is a perfect matching of `G` with the two vertices `u, v` deleted: it fixes
exactly `u` and `v`, and matches every other vertex to a neighbour `≠ u, v`. -/
def IsPMdel (G : SimpleGraph V) (u v : V) (h : V → V) : Prop :=
  Involutive h ∧ h u = u ∧ h v = v ∧
    ∀ w, w ≠ u → w ≠ v → (h w ≠ w ∧ G.Adj w (h w) ∧ h w ≠ u ∧ h w ≠ v)

/-
In a perfect matching containing the edge `uv`, no interior vertex is matched
to `u` or to `v`.
-/

/-- Restriction of a matching `f` to the graph with `u, v` deleted: fix `u, v`,
keep everything else. -/
def restrictPM [DecidableEq V] (u v : V) (f : V → V) : V → V :=
  fun w => if w = u then u else if w = v then v else f w

/-- Extension of a deleted matching `h` back to `G` by swapping `u ↔ v`. -/
def extendPM [DecidableEq V] (u v : V) (h : V → V) : V → V :=
  fun w => if w = u then v else if w = v then u else h w





/-
**Deletion characterisation of forcing edges.**  The edge `uv` is a forcing
edge of `G` iff `uv ∈ E(G)` and the graph with `u, v` deleted has a *unique*
perfect matching.
-/

/-
If `G` has a unique perfect matching `f₀`, then every edge `{v, f₀ v}` of that
matching is a forcing edge.
-/

/-
Forcing is symmetric in the two endpoints of the edge.
-/

end ForcingEdges


