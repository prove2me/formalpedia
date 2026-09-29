-- Prove2me | solution 1 for Hadwiger.hadwigerProperty_of_minDegree_forces
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T11:43:09.913915+00:00
-- url     : https://prove2.me/submissions/2a6cf176-6578-4187-9d6a-ec61f2add781

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_HadwigerSmallCases

open Hadwiger SimpleGraph in
theorem solution {k : ℕ}
    (H : ∀ (W : Type) [Finite W] [Nonempty W] (K : SimpleGraph W),
        (∀ w : W, k ≤ Nat.card (K.neighborSet w)) → CompleteMinor (k + 1) K) :
    HadwigerProperty k := by
  intro V _ G h
  classical
  haveI := Fintype.ofFinite V
  have hcrit : ∃ S : Finset V, S.Nonempty ∧ ¬ ColorableOn G S k ∧
      ∀ v ∈ S, k ≤ (S.filter (fun w => G.Adj v w)).card := by
    have huniv : ¬ ColorableOn G Finset.univ k := by
      rintro ⟨c, hc⟩
      exact h ⟨SimpleGraph.Coloring.mk c
        (fun {x y} hxy => hc x (Finset.mem_univ _) y (Finset.mem_univ _) hxy)⟩
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      have hne : Nonempty V := by
        by_contra hV
        exact h (SimpleGraph.colorable_zero_iff.2 (not_nonempty_iff.1 hV))
      obtain ⟨v⟩ := hne
      refine ⟨{v}, Finset.singleton_nonempty v, ?_, fun _ _ => Nat.zero_le _⟩
      rintro ⟨c, -⟩
      exact (c v).elim0
    · obtain ⟨S, hS, hmin⟩ := Finset.exists_min_image
        ((Finset.univ : Finset (Finset V)).filter (fun S => ¬ ColorableOn G S k)) Finset.card
        ⟨Finset.univ, by simp [huniv]⟩
      rw [Finset.mem_filter] at hS
      have hSne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        exact hS.2 ⟨fun _ => ⟨0, hkpos⟩, by simp⟩
      refine ⟨S, hSne, hS.2, fun v hv => ?_⟩
      by_contra hlt
      have hlt' : (S.filter (fun w => G.Adj v w)).card < k := not_le.1 hlt
      have hcol : ColorableOn G (S.erase v) k := by
        by_contra hnc
        have h1 := hmin (S.erase v) (by simp [hnc])
        have h2 := Finset.card_erase_of_mem hv
        have h3 := Finset.card_pos.2 ⟨v, hv⟩
        omega
      obtain ⟨c, hc⟩ := hcol
      set N := (S.filter (fun w => G.Adj v w)).image c with hN
      have hNcard : N.card < k := lt_of_le_of_lt Finset.card_image_le hlt'
      obtain ⟨col, hcolN⟩ : ∃ col : Fin k, col ∉ N := by
        by_contra hall
        simp only [not_exists, not_not] at hall
        have h1 := Finset.card_le_card (fun x _ => hall x : (Finset.univ : Finset (Fin k)) ⊆ N)
        rw [Finset.card_univ, Fintype.card_fin] at h1
        omega
      apply hS.2
      refine ⟨Function.update c v col, ?_⟩
      intro x hx y hy hxy
      by_cases hxv : x = v <;> by_cases hyv : y = v
      · subst hxv
        subst hyv
        exact absurd hxy G.irrefl
      · subst hxv
        rw [Function.update_self, Function.update_of_ne hyv]
        intro heq
        apply hcolN
        rw [hN, Finset.mem_image]
        exact ⟨y, Finset.mem_filter.2 ⟨hy, hxy⟩, heq.symm⟩
      · subst hyv
        rw [Function.update_of_ne hxv, Function.update_self]
        intro heq
        apply hcolN
        rw [hN, Finset.mem_image]
        exact ⟨x, Finset.mem_filter.2 ⟨hx, G.symm hxy⟩, heq⟩
      · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
        exact hc x (Finset.mem_erase.2 ⟨hxv, hx⟩) y (Finset.mem_erase.2 ⟨hyv, hy⟩) hxy
  obtain ⟨S, hSne, -, hdeg⟩ := hcrit
  obtain ⟨v0, hv0⟩ := hSne
  haveI : Nonempty (↑S : Set V) := ⟨⟨v0, hv0⟩⟩
  have hdegK : ∀ w : (↑S : Set V), k ≤ Nat.card ((G.induce (↑S : Set V)).neighborSet w) := by
    intro w
    have e : (G.induce (↑S : Set V)).neighborSet w ≃ ↥(S.filter (fun u => G.Adj w.1 u)) :=
      { toFun := fun u => ⟨u.1.1, Finset.mem_filter.2 ⟨u.1.2, u.2⟩⟩
        invFun := fun x => ⟨⟨x.1, (Finset.mem_filter.1 x.2).1⟩, (Finset.mem_filter.1 x.2).2⟩
        left_inv := fun u => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hdeg w.1 w.2
  obtain ⟨M⟩ := H (↑S : Set V) (G.induce (↑S : Set V)) hdegK
  refine ⟨{ branch := fun w => Subtype.val '' M.branch w
            branch_nonempty := fun w => (M.branch_nonempty w).image _
            branch_disjoint := fun w w' hww' =>
              (Set.disjoint_image_iff Subtype.val_injective).2 (M.branch_disjoint hww')
            branch_connected := fun w => ?_
            edge_lift := fun a b hab => ?_ }⟩
  · have hc := M.branch_connected w
    let f : (G.induce (↑S : Set V)).induce (M.branch w) →g
        G.induce (Subtype.val '' M.branch w) :=
      { toFun := fun x => ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
        map_rel' := fun {x y} hxy => hxy }
    refine hc.map f ?_
    rintro ⟨y, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · obtain ⟨x, hx, y, hy, hxy⟩ := M.edge_lift hab
    exact ⟨x.1, ⟨x, hx, rfl⟩, y.1, ⟨y, hy, rfl⟩, hxy⟩
