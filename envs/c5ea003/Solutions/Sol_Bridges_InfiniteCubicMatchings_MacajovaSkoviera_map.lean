-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.MacajovaSkoviera.map
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T13:45:32.450264+00:00
-- url     : https://prove2.me/submissions/38a1fb2c-9092-4515-830d-5e9ab115ce3c

-- Sol generated from Bridges/InfiniteCubicMatchings.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
/-
# Perfect matching conjectures in (possibly infinite) cubic bridgeless graphs

This file develops a formal framework, valid for **arbitrary** (finite or infinite) vertex
types, for the three classical perfect-matching conjectures on cubic bridgeless graphs:

* the **Berge–Fulkerson conjecture** (`BergeFulkerson`): six perfect matchings covering
  every edge exactly twice;
* the **Fan–Raspaud conjecture** (`FanRaspaud`): three perfect matchings with empty
  intersection;
* the **Máčajová–Škoviera conjecture** (`MacajovaSkoviera`): two perfect matchings whose
  intersection contains no odd edge cut.

The main results proved here are

* `PerfectMatching.exists_mem_cutEdges` and `PerfectMatching.card_inter_cutEdges_odd`:
  the *parity lemma* in the infinite setting — a perfect matching meets every edge cut with
  a **finite odd side** in an odd (in particular nonzero) number of edges;
* `BergeFulkerson.fanRaspaud` : BF ⟹ FR;
* `FanRaspaud.macajovaSkoviera` : FR ⟹ MŠ (this is where the parity lemma is used);
* `BergeFulkerson.macajovaSkoviera` : BF ⟹ MŠ;
* `not_bergeFulkerson_of_oddCut_singleton` and friends: all three conjectures **fail** for a
  graph possessing a one-edge cut with a finite odd side (the infinite analogue of "a cubic
  graph with a bridge has no such family"); hence bridgelessness is a necessary hypothesis;
* `ProperThreeEdgeColoring.bergeFulkerson` : a 3-edge-colourable graph satisfies BF (by
  doubling the colour classes) — this works verbatim for infinite graphs;
* transport of all three properties along graph isomorphisms.

Everything is stated for an arbitrary vertex type `V`; no finiteness of `V` is assumed
anywhere.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-! ## Perfect matchings as fixed-point-free involutions -/


open PerfectMatching









/-! ## Edge cuts with a finite side -/






/-! ## A combinatorial lemma: fixed-point-free involutions have even orbit sets -/


/-! ## The parity lemma -/

open PerfectMatching

variable (M : PerfectMatching G)






/-! ## The three conjectures -/







/-! ## The implications BF ⟹ FR ⟹ MŠ -/




/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/






/-! ## 3-edge-colourable graphs satisfy Berge–Fulkerson -/


/-! ## Invariance under isomorphism -/

open PerfectMatching

variable {W : Type v} {H : SimpleGraph W}


@[simp] lemma mem_map_edges (f : G ≃g H) (M : PerfectMatching G) (u w : V) :
    s(f u, f w) ∈ (M.map f).edges ↔ s(u, w) ∈ M.edges := by
  simp only [mem_edges, map]
  constructor
  · intro h
    have := congrArg f.symm h
    simpa using this
  · intro h
    rw [show f.symm (f u) = u by simp, h]

lemma mem_map_edges' (f : G ≃g H) (M : PerfectMatching G) (e : Sym2 W) :
    e ∈ (M.map f).edges ↔ Sym2.map f.symm e ∈ M.edges := by
  induction e with
  | _ a b =>
    rw [Sym2.map_pair_eq, show s(a, b) = s(f (f.symm a), f (f.symm b)) by simp]
    exact mem_map_edges f M _ _



/-- The image of a cut edge under an isomorphism matching the two sides is a cut edge. -/
lemma mem_cutEdges_map {W : Type v} {H : SimpleGraph W} (f : G ≃g H) (S : Finset V)
    (T : Finset W) (hST : ∀ v : V, v ∈ S ↔ f v ∈ T) {e : Sym2 V} (he : e ∈ cutEdges G S) :
    Sym2.map f e ∈ cutEdges H T := by
  obtain ⟨heE, u, w, rfl, huS, hwS⟩ := he
  refine ⟨?_, f u, f w, by simp, (hST u).mp huS, fun hc => hwS ((hST w).mpr hc)⟩
  simpa using f.map_adj_iff.mpr (by simpa using heE)





open Bridges.InfiniteCubicMatchings in
theorem solution{W : Type v} {H : SimpleGraph W} (f : G ≃g H)
    (h : MacajovaSkoviera G) : MacajovaSkoviera H := by
  classical
  obtain ⟨M₁, M₂, hM⟩ := h
  refine ⟨M₁.map f, M₂.map f, ?_⟩
  rintro C ⟨T, hT, rfl⟩ hsub
  refine hM (cutEdges G (T.image f.symm)) ⟨T.image f.symm, ?_, rfl⟩ ?_
  · rwa [Finset.card_image_of_injective _ f.symm.injective]
  · intro e he
    have hST : ∀ v : V, v ∈ T.image f.symm ↔ f v ∈ T := by
      intro v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩; simpa using hw
      · intro hv; exact ⟨f v, hv, by simp⟩
    have hmap := mem_cutEdges_map f _ T hST he
    obtain ⟨h1, h2⟩ := hsub hmap
    rw [mem_map_edges'] at h1 h2
    simp only [Sym2.map_map, Function.comp, RelIso.symm_apply_apply, Sym2.map_id'] at h1 h2
    exact ⟨h1, h2⟩
