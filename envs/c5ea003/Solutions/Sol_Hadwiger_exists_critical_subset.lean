-- Prove2me | solution 1 for Hadwiger.exists_critical_subset
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:47:40.40072+00:00
-- url     : https://prove2.me/submissions/70705518-d9bb-4d21-8fab-2bc0c773937b

import Mathlib
import Definitions.Def_Probability_HadwigerCritical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Hadwiger
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

theorem colorableOn_univ_iff [Fintype V] :
    ColorableOn G Finset.univ k ↔ G.Colorable k := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨Coloring.mk c fun {x y} hxy => hc x (mem_univ x) y (mem_univ y) hxy⟩
  · rintro ⟨C⟩
    exact ⟨C, fun x _ y _ hxy => C.valid hxy⟩

omit [DecidableRel G.Adj] in
/-- The empty set is colourable as soon as at least one colour is available. -/
theorem colorableOn_empty (hk : 0 < k) : ColorableOn G ∅ k :=
  ⟨fun _ => ⟨0, hk⟩, by simp⟩

/-! ## 2.  A vertex-minimal non-colourable subset -/

end Hadwiger
open Hadwiger SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} {k : ℕ}
/-- **Existence of a colour-critical subset.**  If `G` is not `k`-colourable,
there is a vertex subset `S` that is not `k`-colourable while every subset with
fewer vertices is. -/
theorem solution [Fintype V] [DecidableEq V] (h : ¬ G.Colorable k) :
    ∃ S : Finset V, ¬ ColorableOn G S k ∧
      ∀ T : Finset V, ¬ ColorableOn G T k → S.card ≤ T.card := by
  classical
  have hex : (Finset.univ.filter (fun S : Finset V => ¬ ColorableOn G S k)).Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    exact fun hcon => h (colorableOn_univ_iff.mp hcon)
  obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image _ Finset.card hex
  rw [mem_filter] at hS
  exact ⟨S, hS.2, fun T hT => hmin T (by simp [hT])⟩


#print axioms solution
