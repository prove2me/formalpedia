-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.bergeFulkerson_iff_locallyApproximable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:30:57.884398+00:00
-- url     : https://prove2.me/submissions/436dcd20-be6b-4e5c-9639-bc55e462312e

-- Sol generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
import Theorems.Thm_Bridges_InfiniteCubicMatchings_bergeFulkerson_of_bfCond
import Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_forall_of_forall_finset
/-
# Compactness: transferring the Berge–Fulkerson property from finite to infinite graphs

The paper *On some perfect matching conjectures in infinite, cubic, bridgeless graphs*
proves that the finite versions of the Berge–Fulkerson, Fan–Raspaud and Máčajová–Škoviera
conjectures are equivalent to their infinite versions.  The engine behind such statements is
a compactness (Rado selection / Tychonoff) argument.  This file formalises that engine.

Main results:

* `exists_forall_of_forall_finset` : a general compactness principle.  A constraint system on
  a product of *finite* sets, each constraint depending only on finitely many coordinates, is
  satisfiable as soon as every finite subsystem is.
* `bergeFulkerson_iff_locallyApproximable` : for a locally finite graph, the Berge–Fulkerson
  property is **finitary**: it holds iff every finite set of vertices carries a partial
  Berge–Fulkerson configuration.  (This is the exact local-to-global content of the transfer
  theorem.)
* `bergeFulkerson_of_finite_local_models` : if the *finite* Berge–Fulkerson conjecture holds
  and the (possibly infinite) locally finite graph `G` admits, around every finite set of
  vertices, a finite cubic bridgeless *local model*, then `G` satisfies Berge–Fulkerson.
-/

open Bridges.InfiniteCubicMatchings

universe u v w

/-! ## A general compactness principle -/


/-! ## Berge–Fulkerson configurations -/

variable {V : Type u} {G : SimpleGraph V}





/-- Conversely, the Berge–Fulkerson property gives a configuration valid at every vertex. -/
theorem exists_bfCond_of_bergeFulkerson (h : BergeFulkerson G) :
    ∃ c : BFConfig G, ∀ v, BFCond G c v := by
  obtain ⟨M, hM⟩ := h
  refine ⟨fun v i => ⟨(M i).partner v, (M i).isAdj v⟩, fun v => ⟨fun i => (M i).invol v, ?_⟩⟩
  intro w hw
  have hE : s(v, w) ∈ G.edgeSet := hw
  have := hM _ hE
  rwa [show {i : Fin 6 | s(v, w) ∈ (M i).edges} = {i : Fin 6 | (M i).partner v = w} by
    ext i; simp] at this


/-! ## Finite local models: the finite conjecture transfers to infinite graphs -/

variable {W : Type v}





/-! ## The same for Fan–Raspaud and Máčajová–Škoviera

All three properties are *finitary*: they are determined by their restrictions to finite sets
of vertices.  We set up the two remaining cases with the same machinery. -/






/-! ### Fan–Raspaud -/




/-! ### Máčajová–Škoviera -/




/-! ### Finite local models for Fan–Raspaud

The same pullback argument as for Berge–Fulkerson, one dimension lower. -/





open Bridges.InfiniteCubicMatchings in
theorem solution(hlf : ∀ v : V, (G.neighborSet v).Finite) :
    BergeFulkerson G ↔ BFLocallyApproximable G := by
  classical
  constructor
  · intro h T
    obtain ⟨c, hc⟩ := exists_bfCond_of_bergeFulkerson h
    exact ⟨c, fun v _ => hc v⟩
  · intro h
    haveI : ∀ v : V, Finite (G.neighborSet v) := fun v => (hlf v).to_subtype
    have hloc : ∀ v : V, ∃ D : Finset V, ∀ c d : BFConfig G,
        (∀ x ∈ D, c x = d x) → BFCond G c v → BFCond G d v := by
      intro v
      refine ⟨insert v (hlf v).toFinset, ?_⟩
      intro c d hagree hcv
      have hv : c v = d v := hagree v (Finset.mem_insert_self _ _)
      constructor
      · intro i
        have h1 : (d v i : V) = (c v i : V) := by rw [hv]
        have hmem : (c v i : V) ∈ insert v (hlf v).toFinset := by
          simp [Set.Finite.mem_toFinset, (c v i).2]
        have h2 : c ((c v i : V)) = d ((c v i : V)) := hagree _ hmem
        rw [h1, ← h2]
        exact hcv.1 i
      · intro w hw
        rw [show {i : Fin 6 | (d v i : V) = w} = {i : Fin 6 | (c v i : V) = w} by rw [hv]]
        exact hcv.2 w hw
    obtain ⟨c, hc⟩ := exists_forall_of_forall_finset (K := fun v : V => Fin 6 → G.neighborSet v)
      (fun v c => BFCond G c v) hloc h
    exact bergeFulkerson_of_bfCond c hc
