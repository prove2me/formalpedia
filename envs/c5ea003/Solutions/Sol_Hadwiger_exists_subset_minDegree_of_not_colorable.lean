-- Prove2me | solution 1 for Hadwiger.exists_subset_minDegree_of_not_colorable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T07:47:41.192588+00:00
-- url     : https://prove2.me/submissions/2f8357bf-50f7-4da2-8764-896edd273d62

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

omit [DecidableRel G.Adj] in
/-- **Existence of a colour-critical subset.**  If `G` is not `k`-colourable,
there is a vertex subset `S` that is not `k`-colourable while every subset with
fewer vertices is. -/
theorem exists_critical_subset [Fintype V] [DecidableEq V] (h : ¬ G.Colorable k) :
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

/-! ## 3.  Critical subsets have large minimum degree -/

/-- **Colour-critical subsets have minimum degree at least `k`.**  If `G` is not
`k`-colourable then some non-empty vertex subset `S` is itself not
`k`-colourable and has the property that every vertex of `S` has at least `k`
neighbours inside `S`. -/
theorem quick_minDegree [Fintype V] [DecidableEq V]
    (h : ¬ G.Colorable k) :
    ∃ S : Finset V, S.Nonempty ∧ ¬ ColorableOn G S k ∧
      ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- with no colours available the degree condition is vacuous
    have hne : (Finset.univ : Finset V).Nonempty := by
      rw [Finset.univ_nonempty_iff]
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact h (G.colorable_zero_iff.mpr hcon)
    exact ⟨Finset.univ, hne, fun hcon => h (colorableOn_univ_iff.mp hcon),
      fun v _ => Nat.zero_le _⟩
  obtain ⟨S, hS, hmin⟩ := exists_critical_subset h
  have hne : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact absurd (colorableOn_empty hk) hS
    · exact hne
  refine ⟨S, hne, hS, fun v hv => ?_⟩
  by_contra hcon
  push_neg at hcon
  -- the graph minus `v` is colourable, by minimality
  have hlt : (S.erase v).card < S.card := by
    rw [Finset.card_erase_of_mem hv]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨v, hv⟩) one_pos
  have hcol : ColorableOn G (S.erase v) k := by
    by_contra hc
    exact absurd (hmin _ hc) (not_le.mpr hlt)
  obtain ⟨c', hc'⟩ := hcol
  -- a colour missed by the (fewer than `k`) neighbours of `v` inside `S`
  set F : Finset (Fin k) := (S.filter (fun w => G.Adj v w)).image c' with hF
  have hFlt : F.card < Fintype.card (Fin k) := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simpa using hcon
  have hss : F ⊂ Finset.univ :=
    Finset.ssubset_univ_iff.mpr fun hcon' => by
      rw [hcon'] at hFlt; simp at hFlt
  obtain ⟨col, -, hcol'⟩ := Finset.exists_of_ssubset hss
  refine hS ⟨Function.update c' v col, ?_⟩
  intro x hx y hy hxy
  by_cases hxv : x = v
  · subst hxv
    have hyv : y ≠ x := hxy.ne'
    rw [Function.update_self, Function.update_of_ne hyv]
    intro heq
    exact hcol' (by
      rw [hF, heq]
      exact Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨hy, hxy⟩))
  · by_cases hyv : y = v
    · subst hyv
      rw [Function.update_self, Function.update_of_ne hxv]
      intro heq
      exact hcol' (by
        rw [hF, ← heq]
        exact Finset.mem_image_of_mem c' (Finset.mem_filter.mpr ⟨hx, hxy.symm⟩))
    · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
      exact hc' x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hxy


end Hadwiger
open Hadwiger SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
theorem solution [Fintype V] [DecidableEq V] (h : ¬ G.Colorable k) :
    ∃ S : Finset V, S.Nonempty ∧ ¬ ColorableOn G S k ∧
      ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card := by
  exact Hadwiger.quick_minDegree h
#print axioms solution
