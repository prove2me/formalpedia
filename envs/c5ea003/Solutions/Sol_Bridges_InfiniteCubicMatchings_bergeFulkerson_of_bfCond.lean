-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.bergeFulkerson_of_bfCond
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:09.856267+00:00
-- url     : https://prove2.me/submissions/d0cba80c-7758-4ae6-8765-8cdc51c12dc2

-- Sol generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
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
theorem solution(c : BFConfig G) (hc : ∀ v, BFCond G c v) :
    BergeFulkerson G := by
  refine ⟨fun i => ⟨fun v => (c v i : V), fun v => (c v i).2, fun v => (hc v).1 i⟩, ?_⟩
  intro e
  induction e with
  | _ u w =>
    intro hE
    have hadj : G.Adj u w := hE
    have : {i : Fin 6 | s(u, w) ∈ (PerfectMatching.mk (fun v => (c v i : V))
        (fun v => (c v i).2) (fun v => (hc v).1 i) : PerfectMatching G).edges}
        = {i : Fin 6 | (c u i : V) = w} := by
      ext i
      simp only [Set.mem_setOf_eq, PerfectMatching.mem_edges]
    rw [this]
    exact (hc u).2 w hadj
