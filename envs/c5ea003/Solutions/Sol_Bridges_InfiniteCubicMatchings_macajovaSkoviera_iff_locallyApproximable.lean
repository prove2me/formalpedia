-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.macajovaSkoviera_iff_locallyApproximable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:05:24.750819+00:00
-- url     : https://prove2.me/submissions/9d618c46-1c3b-45d8-8df6-0f708343c6de

-- Sol generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
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







/-! ## Finite local models: the finite conjecture transfers to infinite graphs -/

variable {W : Type v}





/-! ## The same for Fan–Raspaud and Máčajová–Škoviera

All three properties are *finitary*: they are determined by their restrictions to finite sets
of vertices.  We set up the two remaining cases with the same machinery. -/




@[simp] lemma mem_toMatchings_edges {k : ℕ} (c : MConfig G k) (h : ∀ v, InvolCond G c v)
    (i : Fin k) (u w : V) : s(u, w) ∈ (toMatchings c h i).edges ↔ (c u i : V) = w := by
  simp only [PerfectMatching.mem_edges, toMatchings]

/-- Involutivity at `v` only depends on the coordinates of `v` and of its neighbours. -/
lemma involCond_local {k : ℕ} (v : V) (c d : MConfig G k) (hv : c v = d v)
    (hn : ∀ x ∈ G.neighborSet v, c x = d x) (hcv : InvolCond G c v) : InvolCond G d v := by
  intro i
  have h1 : (d v i : V) = (c v i : V) := by rw [hv]
  have h2 : c ((c v i : V)) = d ((c v i : V)) := hn _ (c v i).2
  rw [h1, ← h2]
  exact hcv i

/-! ### Fan–Raspaud -/




/-! ### Máčajová–Škoviera -/




/-! ### Finite local models for Fan–Raspaud

The same pullback argument as for Berge–Fulkerson, one dimension lower. -/





open Bridges.InfiniteCubicMatchings in
theorem solution(hlf : ∀ v : V, (G.neighborSet v).Finite) :
    MacajovaSkoviera G ↔ MSLocallyApproximable G := by
  classical
  constructor
  · rintro ⟨M₁, M₂, hM⟩ T
    refine ⟨fun v i => ⟨(![M₁, M₂] i).partner v, (![M₁, M₂] i).isAdj v⟩, ?_⟩
    rintro (v | S) -
    · exact fun i => (![M₁, M₂] i).invol v
    · intro hS
      have hnot := hM (cutEdges G S) ⟨S, hS, rfl⟩
      rw [Set.not_subset] at hnot
      obtain ⟨e, heC, heM⟩ := hnot
      obtain ⟨hEe, u, w, rfl, huS, hwS⟩ := heC
      have hadj : G.Adj u w := by simpa using hEe
      refine ⟨u, huS, w, hadj, hwS, ?_⟩
      rintro ⟨h0, h1⟩
      exact heM ⟨by simpa using h0, by simpa using h1⟩
  · intro h
    haveI : ∀ v : V, Finite (G.neighborSet v) := fun v => (hlf v).to_subtype
    have hloc : ∀ j : V ⊕ Finset V, ∃ D : Finset V, ∀ c d : MConfig G 2,
        (∀ x ∈ D, c x = d x) → MSCond G c j → MSCond G d j := by
      rintro (v | S)
      · refine ⟨insert v (hlf v).toFinset, fun c d hagree hcv => ?_⟩
        refine involCond_local v c d (hagree v (Finset.mem_insert_self _ _)) ?_ hcv
        intro x hx
        exact hagree x (Finset.mem_insert_of_mem (by simpa using hx))
      · refine ⟨S, fun c d hagree hcS hS => ?_⟩
        obtain ⟨u, huS, w, hadj, hwS, hne⟩ := hcS hS
        refine ⟨u, huS, w, hadj, hwS, ?_⟩
        rw [← hagree u huS]
        exact hne
    obtain ⟨c, hc⟩ := exists_forall_of_forall_finset
      (K := fun v : V => Fin 2 → G.neighborSet v) (fun j c => MSCond G c j) hloc h
    have hinv : ∀ v, InvolCond G c v := fun v => hc (Sum.inl v)
    refine ⟨toMatchings c hinv 0, toMatchings c hinv 1, ?_⟩
    rintro C ⟨S, hS, rfl⟩ hsub
    obtain ⟨u, huS, w, hadj, hwS, hne⟩ := hc (Sum.inr S) hS
    have hmem : s(u, w) ∈ cutEdges G S := ⟨by simpa using hadj, u, w, rfl, huS, hwS⟩
    obtain ⟨h0, h1⟩ := hsub hmem
    rw [mem_toMatchings_edges] at h0 h1
    exact hne ⟨h0, h1⟩
