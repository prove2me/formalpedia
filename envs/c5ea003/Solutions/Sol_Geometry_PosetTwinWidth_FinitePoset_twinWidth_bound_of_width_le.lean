-- Prove2me | solution 1 for Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:28:16.072651+00:00
-- url     : https://prove2.me/submissions/c78b6e03-4553-48a5-a5c0-c3497f3c7c16

import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
import Definitions.Def_Geometry_PosetTwinWidth_LinearBound

open Geometry.PosetTwinWidth FinitePoset Graph.TwinWidth in
theorem solution {k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
    ∃ seq : List (P.carrier × P.carrier),
      IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card := by
  classical
  haveI := P.ftype
  by_cases hne : Nonempty P.carrier
  · -- contract every vertex into a fixed vertex `v₀`
    obtain ⟨v₀⟩ := hne
    let seq : List (P.carrier × P.carrier) :=
      ((Finset.univ.erase v₀).toList).map (fun v => (v₀, v))
    have hmem : ∀ x, x ≠ v₀ → (v₀, x) ∈ seq := fun x hx =>
      List.mem_map.2 ⟨x, by simp [hx], rfl⟩
    have hto : ∀ x, Relation.ReflTransGen (MergeRel seq) v₀ x := by
      intro x
      by_cases hx : x = v₀
      · subst hx
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (Or.inl (hmem x hx))
    have hfrom : ∀ x, Relation.ReflTransGen (MergeRel seq) x v₀ := by
      intro x
      by_cases hx : x = v₀
      · subst hx
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single (Or.inr (hmem x hx))
    refine ⟨seq, ⟨rfl, ?_, fun a b => (hfrom a).trans (hto b)⟩, ?_⟩
    · intro e he
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 he
      simp only [Finset.mem_toList, Finset.mem_erase] at hv
      exact fun h => hv.1 h.symm
    · rw [List.length_map, Finset.length_toList, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      unfold FinitePoset.card
      simp only [Fintype.card_eq_nat_card]
      omega
  · refine ⟨[], ⟨rfl, by simp, fun a => absurd ⟨a⟩ hne⟩, by simp⟩
