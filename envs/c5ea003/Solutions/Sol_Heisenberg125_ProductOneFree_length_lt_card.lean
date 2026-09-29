-- Prove2me | solution 1 for Heisenberg125.ProductOneFree.length_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:37:28.164072+00:00
-- url     : https://prove2.me/submissions/418def47-4851-4deb-947d-bb22fb489585

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 in
theorem solution {G : Type*} [Group G] [Fintype G] {L : List G} (h : ProductOneFree L) :
    L.length < Fintype.card G := by
  have hblock : ∀ {i j : ℕ}, i < j → j ≤ L.length → (L.take i).prod = (L.take j).prod →
      ∃ T : List G, T.Sublist L ∧ T ≠ [] ∧ T.prod = 1 := by
    intro i j hij hj h
    refine ⟨(L.take j).drop i, ?_, ?_, ?_⟩
    · exact ((L.take j).drop_sublist i).trans (L.take_sublist j)
    · have hlen : ((L.take j).drop i).length = j - i := by
        simp [min_eq_left hj]
      intro hnil
      rw [hnil] at hlen
      simp at hlen
      omega
    · have happ : (L.take i) ++ ((L.take j).drop i) = L.take j := by
        have htt : (L.take j).take i = L.take i := by
          rw [List.take_take, min_eq_left hij.le]
        rw [← htt, List.take_append_drop]
      have hsplit : (L.take i).prod * ((L.take j).drop i).prod = (L.take j).prod := by
        rw [← List.prod_append, happ]
      rw [h] at hsplit
      have hcancel : (L.take j).prod * ((L.take j).drop i).prod = (L.take j).prod * 1 := by
        rw [mul_one]
        exact hsplit
      exact mul_left_cancel hcancel
  by_contra hcon
  push_neg at hcon
  have hcard : Fintype.card G < Fintype.card (Fin (L.length + 1)) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨x, y, hxy, hfxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (L.length + 1) => (L.take (i : ℕ)).prod) hcard
  have hxb : (x : ℕ) ≤ L.length := Nat.lt_succ_iff.mp x.isLt
  have hyb : (y : ℕ) ≤ L.length := Nat.lt_succ_iff.mp y.isLt
  have hne' : (x : ℕ) ≠ (y : ℕ) := fun hh => hxy (Fin.ext hh)
  rcases Nat.lt_or_ge (x : ℕ) (y : ℕ) with hlt | hge
  · obtain ⟨T, hsub, hTne, hprod⟩ := hblock hlt hyb hfxy
    exact h T hsub hTne ⟨T, List.Perm.refl T, hprod⟩
  · have hlt' : (y : ℕ) < (x : ℕ) := by omega
    obtain ⟨T, hsub, hTne, hprod⟩ := hblock hlt' hxb hfxy.symm
    exact h T hsub hTne ⟨T, List.Perm.refl T, hprod⟩
