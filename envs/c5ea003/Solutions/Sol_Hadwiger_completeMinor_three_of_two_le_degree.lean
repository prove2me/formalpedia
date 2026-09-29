-- Prove2me | solution 1 for Hadwiger.completeMinor_three_of_two_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T12:21:09.966638+00:00
-- url     : https://prove2.me/submissions/5e2e077e-e7fd-4a81-a45d-d7564bd4026f

import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_HadwigerSmallCases

open Hadwiger SimpleGraph in
theorem solution {W : Type} [Finite W] [Nonempty W]
    (K : SimpleGraph W)
    (hdeg : ∀ w : W, 2 ≤ Nat.card (K.neighborSet w)) : CompleteMinor 3 K := by
  classical
  haveI := Fintype.ofFinite W
  -- the vertex set of a nonempty chain induces a connected graph
  have hconn : ∀ m : List W, m ≠ [] → List.IsChain K.Adj m → (K.induce {x | x ∈ m}).Connected := by
    intro m
    induction m with
    | nil => intro h; exact absurd rfl h
    | cons a t ih =>
      intro _ hch
      rcases t with _ | ⟨b, t⟩
      · haveI : Nonempty ({x | x ∈ [a]} : Set W) := ⟨⟨a, by simp⟩⟩
        refine Connected.mk (fun x y => ?_)
        have hx : x.1 = a := by simpa using x.2
        have hy : y.1 = a := by simpa using y.2
        have hxy : x = y := Subtype.ext (hx.trans hy.symm)
        subst hxy
        exact Reachable.refl _
      · rw [List.isChain_cons_cons] at hch
        obtain ⟨hab, hch'⟩ := hch
        have hbt := ih (List.cons_ne_nil b t) hch'
        have hsub : ({x | x ∈ b :: t} : Set W) ≤ {x | x ∈ a :: b :: t} := by
          intro x hx
          simp only [Set.mem_setOf_eq, List.mem_cons] at hx ⊢
          tauto
        haveI : Nonempty ({x | x ∈ a :: b :: t} : Set W) := ⟨⟨a, by simp⟩⟩
        have hb : b ∈ ({x | x ∈ a :: b :: t} : Set W) := by simp
        have hreach : ∀ x : ({x | x ∈ a :: b :: t} : Set W),
            (K.induce {x | x ∈ a :: b :: t}).Reachable ⟨b, hb⟩ x := by
          intro x
          by_cases hxa : x.1 = a
          · have hadj : (K.induce {x | x ∈ a :: b :: t}).Adj ⟨b, hb⟩ x := by
              show K.Adj b x.1
              rw [hxa]
              exact K.symm hab
            exact hadj.reachable
          · have hx' : x.1 ∈ ({x | x ∈ b :: t} : Set W) := by
              have := x.2
              simp only [Set.mem_setOf_eq, List.mem_cons] at this ⊢
              tauto
            exact (hbt.preconnected ⟨b, by simp⟩ ⟨x.1, hx'⟩).map (K.induceHomOfLE hsub).toHom
        exact Connected.mk (fun x y => (hreach x).symm.trans (hreach y))
  -- a longest path
  set PL : Set ℕ := {n | ∃ l : List W, l.Nodup ∧ List.IsChain K.Adj l ∧ l ≠ [] ∧ l.length = n} with hPL
  have hbdd : BddAbove PL := ⟨Fintype.card W, by
    rintro n ⟨l, hnd, -, -, rfl⟩
    exact hnd.length_le_card⟩
  obtain ⟨w0⟩ := ‹Nonempty W›
  have hne : PL.Nonempty :=
    ⟨1, [w0], List.nodup_singleton _, List.isChain_singleton _, List.cons_ne_nil _ _, rfl⟩
  obtain ⟨l, hnd, hch, hlne, hlen⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ l' : List W, l'.Nodup → List.IsChain K.Adj l' → l'.length ≤ l.length := by
    intro l' h1 h2
    rcases eq_or_ne l' [] with h | h
    · simp [h]
    · rw [hlen]
      exact le_csSup hbdd ⟨l', h1, h2, h, rfl⟩
  obtain ⟨v0, r, rfl⟩ := List.exists_cons_of_ne_nil hlne
  -- every neighbour of `v0` lies on the path
  have hnbr : ∀ u, K.Adj v0 u → u ∈ v0 :: r := by
    intro u hu
    by_contra hnot
    have h := hmax (u :: v0 :: r) (List.nodup_cons.2 ⟨hnot, hnd⟩) (List.isChain_cons_cons.2 ⟨K.symm hu, hch⟩)
    simp at h
  -- two distinct neighbours
  haveI : Nontrivial (K.neighborSet v0) := Fintype.one_lt_card_iff_nontrivial.1 (by
    rw [← Nat.card_eq_fintype_card]
    linarith [hdeg v0])
  obtain ⟨⟨u1, hu1⟩, ⟨u2, hu2⟩, hu12⟩ := exists_pair_ne (K.neighborSet v0)
  have hu1' : K.Adj v0 u1 := hu1
  have hu2' : K.Adj v0 u2 := hu2
  have hu1r : u1 ∈ r := by
    rcases List.mem_cons.1 (hnbr u1 hu1') with h | h
    · exact absurd h.symm (K.ne_of_adj hu1')
    · exact h
  obtain ⟨v1, r', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hu1r)
  have hmem : ∀ x, K.Adj v0 x → x ≠ v1 → x ∈ r' := by
    intro x hx hxv1
    rcases List.mem_cons.1 (hnbr x hx) with h | h
    · exact absurd h.symm (K.ne_of_adj hx)
    · rcases List.mem_cons.1 h with h' | h'
      · exact absurd h' hxv1
      · exact h'
  obtain ⟨u, hu, hur'⟩ : ∃ u, K.Adj v0 u ∧ u ∈ r' := by
    by_cases h1 : u1 = v1
    · exact ⟨u2, hu2', hmem u2 hu2' (fun h2 => hu12 (Subtype.ext (h1.trans h2.symm)))⟩
    · exact ⟨u1, hu1', hmem u1 hu1' h1⟩
  obtain ⟨v2, r'', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hur')
  rw [List.isChain_cons_cons, List.isChain_cons_cons] at hch
  obtain ⟨h01, h12, hch2⟩ := hch
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨hv0, hv1, -⟩ := hnd
  have hv01 : v0 ≠ v1 := fun h => hv0 (by simp [h])
  have hv0r : v0 ∉ v2 :: r'' := fun h => hv0 (List.mem_cons_of_mem _ h)
  have hv10 : v1 ≠ v0 := hv01.symm
  have hv1r : v1 ∉ v2 :: r'' := hv1
  -- the three branch sets
  refine ⟨{ branch := ![{x | x ∈ [v0]}, {x | x ∈ [v1]}, {x | x ∈ v2 :: r''}]
            branch_nonempty := ?_
            branch_disjoint := ?_
            branch_connected := ?_
            edge_lift := ?_ }⟩
  · intro i
    fin_cases i
    · exact ⟨v0, by simp⟩
    · exact ⟨v1, by simp⟩
    · exact ⟨v2, by simp⟩
  · intro i j hij
    have key : ∀ (A B : List W), (∀ x, x ∈ A → x ∉ B) →
        Disjoint ({x | x ∈ A} : Set W) {x | x ∈ B} :=
      fun A B h => Set.disjoint_left.2 (fun x hx hx' => h x hx hx')
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact key [v0] [v1] (by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx, List.mem_singleton]
        exact hv01)
    · exact key [v0] (v2 :: r'') (by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx]
        exact hv0r)
    · exact key [v1] [v0] (by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx, List.mem_singleton]
        exact hv10)
    · exact absurd rfl hij
    · exact key [v1] (v2 :: r'') (by
        intro x hx
        rw [List.mem_singleton] at hx
        rw [hx]
        exact hv1r)
    · exact key (v2 :: r'') [v0] (by
        intro x hx hx'
        rw [List.mem_singleton] at hx'
        rw [hx'] at hx
        exact hv0r hx)
    · exact key (v2 :: r'') [v1] (by
        intro x hx hx'
        rw [List.mem_singleton] at hx'
        rw [hx'] at hx
        exact hv1r hx)
    · exact absurd rfl hij
  · intro i
    fin_cases i
    · exact hconn [v0] (List.cons_ne_nil _ _) (List.isChain_singleton _)
    · exact hconn [v1] (List.cons_ne_nil _ _) (List.isChain_singleton _)
    · exact hconn (v2 :: r'') (List.cons_ne_nil _ _) hch2
  · intro a b hab
    fin_cases a <;> fin_cases b
    · exact absurd hab (by simp)
    · exact ⟨v0, by simp, v1, by simp, h01⟩
    · exact ⟨v0, by simp, u, by simpa using hur', hu⟩
    · exact ⟨v1, by simp, v0, by simp, K.symm h01⟩
    · exact absurd hab (by simp)
    · exact ⟨v1, by simp, v2, by simp, h12⟩
    · exact ⟨u, by simpa using hur', v0, by simp, K.symm hu⟩
    · exact ⟨v2, by simp, v1, by simp, K.symm h12⟩
    · exact absurd hab (by simp)
