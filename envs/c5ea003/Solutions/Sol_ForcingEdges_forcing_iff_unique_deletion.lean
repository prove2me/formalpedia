-- Prove2me | solution 1 for ForcingEdges.forcing_iff_unique_deletion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:42:04.799616+00:00
-- url     : https://prove2.me/submissions/2476a8ef-3d9e-48b8-aa2a-047c2e1c5206

-- Sol generated from Speculative/NumberTheory/Basic.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_Basic
import Theorems.Thm_ForcingEdges_extendPM_isPM

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
theorem IsPM.apply_ne {G : SimpleGraph V} {f : V → V} (hf : IsPM G f) {u v : V}
    (huv : f u = v) {w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    f w ≠ u ∧ f w ≠ v := by
  have := hf.1 w; have := hf.1 u; aesop;



theorem restrictPM_isPMdel [DecidableEq V] {G : SimpleGraph V} {f : V → V}
    (hf : IsPM G f) {u v : V} (huv : f u = v) (hne : u ≠ v) :
    IsPMdel G u v (restrictPM u v f) := by
  have := hf.1;
  refine' ⟨ _, _, _, _ ⟩ <;> simp_all +decide [ Involutive, restrictPM ];
  · grind +ring;
  · exact fun w hwu hwv => ⟨ hf.2.1 w, hf.2.2 w, by have := IsPM.apply_ne hf huv hwu hwv; tauto, by have := IsPM.apply_ne hf huv hwu hwv; tauto ⟩


theorem restrictPM_extendPM [DecidableEq V] {G : SimpleGraph V} {u v : V} {h : V → V}
    (hh : IsPMdel G u v h) (hne : u ≠ v) :
    restrictPM u v (extendPM u v h) = h := by
  funext w; cases eq_or_ne w u <;> cases eq_or_ne w v <;> simp_all +decide [ restrictPM, extendPM ] ;
  · exact hh.2.1.symm;
  · exact hh.2.2.1.symm

theorem extendPM_restrictPM [DecidableEq V] {G : SimpleGraph V} {f : V → V}
    (hf : IsPM G f) {u v : V} (huv : f u = v) (hne : u ≠ v) :
    extendPM u v (restrictPM u v f) = f := by
  funext w; by_cases hw : w = u <;> by_cases hw' : w = v <;> simp_all +decide [ extendPM, restrictPM ] ;
  have := hf.1 u; aesop;

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
theorem solution[DecidableEq V] (G : SimpleGraph V) (u v : V) :
    Forcing G u v ↔ G.Adj u v ∧ ∃! h, IsPMdel G u v h := by
  constructor <;> intro h;
  · obtain ⟨hadj, f₀, hf₀⟩ := h;
    refine' ⟨ hadj, restrictPM u v f₀, _, _ ⟩;
    · exact restrictPM_isPMdel hf₀.1.1 hf₀.1.2 hadj.ne;
    · intro h hh;
      have := hf₀.2 ( extendPM u v h ) ?_;
      · rw [ ← this, restrictPM_extendPM hh hadj.ne ];
      · exact extendPM_isPM hh hadj;
  · obtain ⟨hadj, ⟨h₀, ⟨hpmdel₀, huniq⟩⟩⟩ := h;
    use hadj;
    use extendPM u v h₀;
    constructor;
    · exact extendPM_isPM hpmdel₀ hadj;
    · intro f hf;
      rw [ ← huniq ( restrictPM u v f ) ( restrictPM_isPMdel hf.1 hf.2 ( hadj.ne ) ), extendPM_restrictPM hf.1 hf.2 ( hadj.ne ) ]
