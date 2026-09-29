-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.fanRaspaud_iff_locallyApproximable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:42:37.963228+00:00
-- url     : https://prove2.me/submissions/95e89f9b-f6f6-4208-99c2-a8f8ee4a02e5

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
    FanRaspaud G ↔ FRLocallyApproximable G := by
  classical
  constructor
  · rintro ⟨M, hM⟩ T
    refine ⟨fun v i => ⟨(M i).partner v, (M i).isAdj v⟩, fun v _ => ⟨fun i => (M i).invol v, ?_⟩⟩
    intro w hw hall
    have : s(v, w) ∈ (M 0).edges ∩ (M 1).edges ∩ (M 2).edges := by
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> rw [PerfectMatching.mem_edges]
      · exact hall 0
      · exact hall 1
      · exact hall 2
    rw [hM] at this
    exact this
  · intro h
    haveI : ∀ v : V, Finite (G.neighborSet v) := fun v => (hlf v).to_subtype
    have hloc : ∀ v : V, ∃ D : Finset V, ∀ c d : MConfig G 3,
        (∀ x ∈ D, c x = d x) → FRCond G c v → FRCond G d v := by
      intro v
      refine ⟨insert v (hlf v).toFinset, fun c d hagree hcv => ⟨?_, ?_⟩⟩
      · refine involCond_local v c d (hagree v (Finset.mem_insert_self _ _)) ?_ hcv.1
        intro x hx
        exact hagree x (Finset.mem_insert_of_mem (by simpa using hx))
      · have hv : c v = d v := hagree v (Finset.mem_insert_self _ _)
        intro w hw hall
        exact hcv.2 w hw (fun i => by rw [hv]; exact hall i)
    obtain ⟨c, hc⟩ := exists_forall_of_forall_finset (K := fun v : V => Fin 3 → G.neighborSet v)
      (fun v c => FRCond G c v) hloc h
    refine ⟨toMatchings c (fun v => (hc v).1), ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro e
    induction e with
    | _ u w =>
      rintro ⟨⟨h0, h1⟩, h2⟩
      rw [mem_toMatchings_edges] at h0 h1 h2
      have hadj : G.Adj u w := by
        have : G.Adj u (c u 0 : V) := (c u 0).2
        rwa [h0] at this
      refine (hc u).2 w hadj (fun i => ?_)
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
