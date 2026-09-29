-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.exists_forall_of_forall_finset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:26:10.362859+00:00
-- url     : https://prove2.me/submissions/e61dd513-bc22-40e8-b5a2-494c70b4d0c2

-- Sol generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
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
theorem solution{ι : Type u} {K : ι → Type v} [∀ i, Finite (K i)]
    {J : Type w} (P : J → (∀ i, K i) → Prop)
    (hloc : ∀ j, ∃ D : Finset ι, ∀ c d : (∀ i, K i), (∀ i ∈ D, c i = d i) → P j c → P j d)
    (hfin : ∀ T : Finset J, ∃ c, ∀ j ∈ T, P j c) :
    ∃ c, ∀ j, P j c := by
  classical
  letI : ∀ i, TopologicalSpace (K i) := fun _ => ⊥
  haveI : ∀ i, DiscreteTopology (K i) := fun _ => ⟨rfl⟩
  haveI : ∀ i, CompactSpace (K i) := fun _ => Finite.compactSpace
  haveI : CompactSpace (∀ i, K i) := Pi.compactSpace
  set S : J → Set (∀ i, K i) := fun j => {c | P j c} with hS
  -- each constraint set is clopen, being determined by finitely many coordinates
  have hcyl : ∀ (D : Finset ι) (c : ∀ i, K i),
      IsOpen {d : ∀ i, K i | ∀ i ∈ D, c i = d i} := by
    intro D c
    have : {d : ∀ i, K i | ∀ i ∈ D, c i = d i} = ⋂ i ∈ D, (fun d : ∀ i, K i => d i) ⁻¹' {c i} := by
      ext d; simp [eq_comm]
    rw [this]
    exact isOpen_biInter_finset fun i _ => (continuous_apply i).isOpen_preimage _ (isOpen_discrete _)
  have hclosed : ∀ j, IsClosed (S j) := by
    intro j
    obtain ⟨D, hD⟩ := hloc j
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_forall_mem_open]
    intro c hc
    refine ⟨{d | ∀ i ∈ D, c i = d i}, ?_, hcyl D c, fun i _ => rfl⟩
    intro d hd hdS
    exact hc (hD d c (fun i hi => (hd i hi).symm) hdS)
  have hne : ∀ T : Finset J, (⋂ j ∈ T, S j).Nonempty := by
    intro T
    obtain ⟨c, hc⟩ := hfin T
    exact ⟨c, by simpa [hS] using hc⟩
  obtain ⟨c, hc⟩ := CompactSpace.iInter_nonempty hclosed hne
  exact ⟨c, fun j => Set.mem_iInter.mp hc j⟩
