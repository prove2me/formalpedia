-- Prove2me | solution 1 for Heisenberg125.Heis.productOneFree_cosetExtremalSeq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T20:28:22.370972+00:00
-- url     : https://prove2.me/submissions/c63704f1-b843-4c4b-8f63-7806be726613

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound
import Definitions.Def_Algebra_Heisenberg125_LowerBound

open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (hp : 0 < p) : ProductOneFree (cosetExtremalSeq p) := by
  have hab : ∀ L : List (Heis p),
      L.prod.a = (L.map Heis.a).sum ∧ L.prod.b = (L.map Heis.b).sum := by
    intro L
    induction L with
    | nil => exact ⟨rfl, rfl⟩
    | cons g L ih =>
      simp only [List.prod_cons, List.map_cons, List.sum_cons, mul_a, mul_b, ih.1, ih.2]
      exact ⟨trivial, trivial⟩
  have hsmall : ∀ i : ℕ, i < p → (i : ZMod p) = 0 → i = 0 := by
    intro i hi h
    have hd : p ∣ i := (CharP.cast_eq_zero_iff (ZMod p) p i).1 h
    exact Nat.eq_zero_of_dvd_of_lt hd hi
  -- with all second coordinates zero, the third coordinate of a product is additive
  have hc0 : ∀ L : List (Heis p), (∀ g ∈ L, g.b = 0) → L.prod.c = (L.map Heis.c).sum := by
    intro L hL
    induction L with
    | nil => rfl
    | cons g L ih =>
      have hL' : ∀ g ∈ L, g.b = 0 := fun g hg => hL g (List.mem_cons_of_mem _ hg)
      have hb0 : L.prod.b = 0 := by
        rw [(hab L).2]
        have : L.map Heis.b = L.map (fun _ => (0 : ZMod p)) := List.map_congr_left hL'
        rw [this]
        simp
      simp only [List.prod_cons, List.map_cons, List.sum_cons, mul_c, hb0, mul_zero, add_zero,
        ih hL']
  intro T hT hne ⟨M, hM, hprod⟩
  unfold cosetExtremalSeq at hT
  obtain ⟨T1, T2, rfl, h1, h2⟩ := List.sublist_append_iff.1 hT
  obtain ⟨i, hi, rfl⟩ := List.sublist_replicate_iff.1 h1
  obtain ⟨j, hj, rfl⟩ := List.sublist_replicate_iff.1 h2
  have hMb : ∀ g ∈ M, g.b = 0 := by
    intro g hg
    have hg' := hM.mem_iff.1 hg
    simp only [List.mem_append, List.mem_replicate] at hg'
    rcases hg' with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl
  have hC : (j : ZMod p) = 0 := by
    have e : ((List.replicate i (⟨1, 0, 0⟩ : Heis p) ++ List.replicate j (⟨1, 0, 1⟩ : Heis p)).map
        Heis.c).sum = (j : ZMod p) := by
      simp
    rw [← e, ← (hM.map Heis.c).sum_eq, ← hc0 M hMb, hprod]
    rfl
  have hj0 := hsmall j (by omega) hC
  subst hj0
  have hA : (i : ZMod p) = 0 := by
    have e : ((List.replicate i (⟨1, 0, 0⟩ : Heis p) ++ List.replicate 0 (⟨1, 0, 1⟩ : Heis p)).map
        Heis.a).sum = (i : ZMod p) := by
      simp
    rw [← e, ← (hM.map Heis.a).sum_eq, ← (hab M).1, hprod]
    rfl
  have hi0 := hsmall i (by omega) hA
  subst hi0
  exact hne rfl
