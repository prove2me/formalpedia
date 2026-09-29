-- Prove2me | solution 1 for ForcingEdges.extendPM_isPM
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:40:38.687766+00:00
-- url     : https://prove2.me/submissions/7cc6d2d9-61c1-4adf-8352-a154c4d3cf69

-- Sol generated from Speculative/NumberTheory/Basic.lean
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


open ForcingEdges in
theorem solution[DecidableEq V] {G : SimpleGraph V} {u v : V} {h : V → V}
    (hh : IsPMdel G u v h) (hadj : G.Adj u v) :
    IsPM G (extendPM u v h) ∧ extendPM u v h u = v := by
  constructor;
  · refine' ⟨ _, _, _ ⟩;
    · intro w; unfold extendPM; by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp +decide [ * ] ;
      have := hh.2.2.2 w hwu hwv; split_ifs <;> simp_all +decide ;
      exact hh.1 _;
    · intro w; cases eq_or_ne w u <;> cases eq_or_ne w v <;> simp_all +decide [ extendPM ] ;
      · grind +splitImp;
      · grind;
      · exact hh.2.2.2 w ‹_› ‹_› |>.1;
    · intro w; by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp_all +decide [ extendPM ] ;
      · exact hadj.symm;
      · exact hh.2.2.2 w hwu hwv |>.2.1;
  · unfold extendPM; aesop;
