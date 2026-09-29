-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.exists_frCond_of_localIso
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:42:36.947911+00:00
-- url     : https://prove2.me/submissions/9a1da67d-47f5-4690-b4ca-0b22dc65eed1

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
theorem solution{K : SimpleGraph W} (φ : V → W) (M : Fin 3 → PerfectMatching K)
    (hM : (M 0).edges ∩ (M 1).edges ∩ (M 2).edges = ∅)
    (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
    ∃ c : MConfig G 3, ∀ v, P v → (∀ x, G.Adj v x → P x) → FRCond G c v := by
  classical
  have key : ∀ v : V, ∀ i : Fin 3, ∃ x : V, G.Adj v x ∧ (P v → φ x = (M i).partner (φ v)) := by
    intro v i
    by_cases h : P v
    · obtain ⟨x, hx, hxe⟩ := (hP v h).surj ((M i).partner (φ v)) ((M i).isAdj (φ v))
      exact ⟨x, hx, fun _ => hxe⟩
    · obtain ⟨x, hx⟩ := hne v
      exact ⟨x, hx, fun h' => absurd h' h⟩
  choose x hadj hphi using key
  refine ⟨fun v i => ⟨x v i, hadj v i⟩, ?_⟩
  intro v hv hvn
  constructor
  · intro i
    have h1 : φ (x v i) = (M i).partner (φ v) := hphi v i hv
    have hPw : P (x v i) := hvn _ (hadj v i)
    have h2 : φ (x (x v i) i) = (M i).partner (φ (x v i)) := hphi _ i hPw
    rw [h1, (M i).invol] at h2
    exact (hP _ hPw).inj _ _ (hadj (x v i) i) (hadj v i).symm h2
  · intro w hw hall
    have hall' : ∀ i : Fin 3, x v i = w := hall
    have h : ∀ i : Fin 3, s(φ v, φ w) ∈ (M i).edges := by
      intro i
      rw [PerfectMatching.mem_edges, ← hphi v i hv, hall' i]
    have hmem : s(φ v, φ w) ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges := ⟨⟨h 0, h 1⟩, h 2⟩
    rw [hM] at hmem
    exact hmem
