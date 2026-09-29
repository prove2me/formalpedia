-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.bergeFulkerson_of_finite_local_models
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:33:51.851602+00:00
-- url     : https://prove2.me/submissions/43b970ca-2ee1-4386-af2d-7e9e5fbf3264

-- Sol generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Theorems.Thm_Bridges_InfiniteCubicMatchings_bergeFulkerson_iff_locallyApproximable
import Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_bfCond_of_localIso
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
theorem solution    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (hBF : FiniteBergeFulkersonConjecture)
    (hmodels : ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
        IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v) :
    BergeFulkerson G := by
  classical
  rw [bergeFulkerson_iff_locallyApproximable hlf]
  intro T
  set T' : Finset V := T ∪ T.biUnion (fun v => (hlf v).toFinset) with hT'
  obtain ⟨W, hWfin, K, φ, hcub, hbr, hiso⟩ := hmodels T'
  obtain ⟨M, hM⟩ := hBF W hWfin K hcub hbr
  obtain ⟨c, hc⟩ := exists_bfCond_of_localIso (G := G) φ M hM hne (fun v => v ∈ T')
    (fun v hv => hiso v hv)
  refine ⟨c, fun v hv => hc v ?_ ?_⟩
  · exact Finset.mem_union_left _ hv
  · intro y hy
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩)
    simpa using hy
