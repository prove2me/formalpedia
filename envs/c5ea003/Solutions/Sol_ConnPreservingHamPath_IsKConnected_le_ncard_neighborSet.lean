-- Prove2me | solution 1 for ConnPreservingHamPath.IsKConnected.le_ncard_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:43.897284+00:00
-- url     : https://prove2.me/submissions/13b29e9a-168b-44e0-af76-c02c7e1e36f3

-- Sol generated from Bridges/Connectivity.lean
import Mathlib
import Definitions.Def_Bridges_Connectivity

/-!
# Vertex `k`-connectivity and the degree necessary condition

Mathlib has edge connectivity and `Connected`, but no notion of vertex
`k`-connectivity (the object at the heart of the connectivity-preserving
Hamiltonian-path program of Hasunuma 2025 and the prescribed-end strengthening).
We supply the standard cut-based definition and prove the classical
**necessary degree condition** that vertex `k`-connectivity forces minimum degree
at least `k` — the easy half of the Whitney/Menger inequality
`κ(G) ≤ δ(G)`.

## Main definitions and results

* `IsKConnected G k` — `G` has more than `k` vertices and deleting any fewer
  than `k` vertices leaves a connected graph.
* `Connected.exists_adj_of_ne` — in a connected graph with two distinct
  vertices, every vertex has a neighbor.
* `IsKConnected.le_ncard_neighborSet` — **`κ(G) ≤ δ(G)`**: in a
  `k`-connected graph every vertex has degree at least `k`.
* `Conjecture_4k4` — the precise (open) research conjecture, recorded as a `Prop`.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): for a connectivity-preserving deletion theorem one
  must control connectivity, so a vertex-cut definition is unavoidable.  We
  conjectured the classical `κ ≤ δ` bound holds with the cut-based definition.
* Experiment (Experimenter): defined `IsKConnected` via induced subgraphs on
  vertex-set complements and proved `κ ≤ δ` by the textbook argument — if some
  vertex `w` had degree `< k`, its neighborhood is a cut of size `< k` isolating
  `w`, contradicting connectivity of the deletion.
* Analysis (Analyst): the proof needs the "no isolated vertex in a connected
  graph on `≥ 2` vertices" lemma (`exists_adj_of_ne`), extracted separately.
  The cardinality slack `card V - (k-1) ≥ 2` is exactly where `k < card V`
  is consumed (the `h_singleton` case split).
* Critique (Critic): this is only the *necessary* direction. The converse
  (Chartrand–Harary: `δ ≥ (n+k-2)/2 ⇒ κ ≥ k`) is strictly deeper and is *not*
  claimed here; it is recorded as a future direction.  The definition is guarded
  by `k < card V` so the empty/complete-graph corner cases are handled.
-- !-- end Lab Notes -- !--
-/

open SimpleGraph

open ConnPreservingHamPath

variable {V : Type*}






open ConnPreservingHamPath in
theorem solution[Fintype V] {G : SimpleGraph V} {k : ℕ}
    (h : IsKConnected G k) (w : V) : k ≤ (G.neighborSet w).ncard := by
  contrapose! h
  intro h'
  have h_connected : (G.induce ((G.neighborSet w : Set V)ᶜ)).Connected := by
    convert h'.2 (G.neighborFinset w) ?_
    all_goals try exact Fintype.ofFinite _
    · aesop
    · aesop
    · simpa [← Set.ncard_coe_finset] using h
  obtain ⟨c, hc⟩ : ∃ c : {v : V // v ∉ G.neighborSet w},
      (G.induce ((G.neighborSet w : Set V)ᶜ)).Adj ⟨w, by simp⟩ c := by
    obtain ⟨c, hc⟩ : ∃ c : {v : V // v ∉ G.neighborSet w}, c ≠ ⟨w, by simp⟩ := by
      by_cases h_singleton : (G.neighborSet w : Set V)ᶜ = {w}
      · have := h'.1
        simp_all +decide
        have := Set.ncard_add_ncard_compl (G.neighborSet w)
        simp_all +decide
        linarith
      · simp_all +decide [Set.eq_singleton_iff_unique_mem]
    have := h_connected ⟨w, by simp⟩ c
    obtain ⟨p⟩ := this
    cases p <;> tauto
  exact c.2 (by simpa using hc)
