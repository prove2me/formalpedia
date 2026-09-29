-- Prove2me | solution 1 for SimpleGraph.colorable_maxDegree_succ
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:30:53.918719+00:00
-- url     : https://prove2.me/submissions/944369ab-1e14-47da-ba9a-9d8862adc65c

-- Sol generated from Novelty/GreedyDegreeColoring.lean
import Mathlib

/-!
# Greedy colouring: a finite graph is `(Δ+1)`-colourable

The classical greedy bound `χ(G) ≤ Δ(G) + 1` for the maximum degree `Δ(G)`.  We build a proper
colouring `V → Fin (maxDegree + 1)` by processing the vertices one at a time (induction on the
processed `Finset`), each time choosing a colour avoided by the already-considered neighbours.
Since every vertex has at most `maxDegree` neighbours, one of the `maxDegree + 1` colours is
always free.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the `1/(Δ+1)` independence-ratio floor is realised by a genuinely
constructive colouring, not merely an existence statement; greedy suffices.
Experiment (Experimenter): induct over the vertex set as a `Finset`; at each `insert v s`, the
colours used on `v`'s neighbours form a set of size `≤ degree v ≤ maxDegree`, so by pigeonhole
(`Finset.card_image_le` + a cardinality contradiction) `Fin (maxDegree+1)` has a free colour;
patch the previous colouring at `v` only.
Analysis (Analyst): correctness of the patch is local — recolouring `v` cannot break an edge
`{x,w}` with `x,w ≠ v`, and the freshly chosen colour is unequal to every neighbour's colour by
construction, in both orientations of the edge.
Critique (Critic): the only subtlety is edges incident to `v`; both `v–w` (new vs old) and
`x–v` (old vs new) are handled by the "free colour" property via `neighborFinset` symmetry.
Synthesis (PI): this constructive `(Δ+1)`-colouring is the engine that converts a bounded-degree
hypothesis into an independence-ratio floor `1/(Δ+1)`, and in particular `Δ ≤ 3 ⇒ i(G) ≥ 1/4`.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]



open SimpleGraph in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] :
    G.Colorable (G.maxDegree + 1) := by
  suffices h : ∃ c : V → Fin (G.maxDegree + 1),
      ∀ v ∈ (Finset.univ : Finset V), ∀ w ∈ G.neighborFinset v, c v ≠ c w by
    obtain ⟨c, hc⟩ := h
    refine ⟨Coloring.mk c ?_⟩
    intro v w hvw
    exact hc v (Finset.mem_univ v) w ((G.mem_neighborFinset v w).mpr hvw)
  -- Build the colouring greedily over an arbitrary processed set of vertices.
  suffices h : ∀ (s : Finset V), ∃ c : V → Fin (G.maxDegree + 1),
      ∀ v ∈ s, ∀ w ∈ G.neighborFinset v, c v ≠ c w from h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert v s hvs ih =>
      obtain ⟨c, hc⟩ := ih
      -- A colour not used by v's neighbours exists (there are at most maxDegree of them).
      obtain ⟨cv, hcv⟩ : ∃ cv : Fin (G.maxDegree + 1),
          cv ∉ Finset.image c (G.neighborFinset v) := by
        have hcard : (Finset.image c (G.neighborFinset v)).card ≤ G.maxDegree :=
          Finset.card_image_le.trans (by simpa using G.degree_le_maxDegree v)
        by_contra hcon
        push_neg at hcon
        have : (Finset.image c (G.neighborFinset v)) = Finset.univ :=
          Finset.eq_univ_of_forall hcon
        rw [this] at hcard
        simp at hcard
      -- Patch the previous colouring: give `v` the free colour `cv`.
      refine ⟨fun w => if w = v then cv else c w, ?_⟩
      intro x hx w hw
      have hxw : G.Adj x w := (G.mem_neighborFinset x w).mp hw
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · -- x = v : the new colour cv differs from every neighbour's colour.
        have hwv : w ≠ x := (G.ne_of_adj hxw).symm
        simp only [if_neg hwv]
        intro h
        exact hcv (Finset.mem_image.mpr ⟨w, hw, h.symm⟩)
      · -- x ∈ s : x ≠ v.
        have hxv : x ≠ v := fun h => hvs (h ▸ hxs)
        simp only [if_neg hxv]
        by_cases hwv : w = v
        · -- w = v : need c x ≠ cv, again from the free-colour property (via symmetry).
          subst hwv
          intro h
          rw [if_pos rfl] at h
          exact hcv (Finset.mem_image.mpr
            ⟨x, (G.mem_neighborFinset w x).mpr (G.symm hxw), h⟩)
        · -- w ≠ v : both x and w keep their old colours; use the IH.
          simp only [if_neg hwv]
          exact hc x hxs w hw
