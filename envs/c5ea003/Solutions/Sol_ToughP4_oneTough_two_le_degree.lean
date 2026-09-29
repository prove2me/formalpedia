-- Prove2me | solution 1 for ToughP4.oneTough_two_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T17:50:05.368364+00:00
-- url     : https://prove2.me/submissions/5fdb915a-a718-4384-99fd-a33e63361d5c

import Mathlib
import Definitions.Def_Bridges_MinimallyToughP4Free
open ToughP4 SimpleGraph Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOneTough G) (hcard : 3 ≤ Fintype.card V) (v : V) :
    2 ≤ (G.neighborSet v).ncard := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  -- connectivity gives `v` a neighbour `u`
  have hfirst : ∀ w, w ≠ v → G.Reachable v w → ∃ x, G.Adj v x := by
    rintro w hw ⟨p⟩
    cases p with
    | nil => exact absurd rfl hw
    | cons h _ => exact ⟨_, h⟩
  obtain ⟨w0, hw0⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card V) v
  obtain ⟨u, hu⟩ := hfirst w0 hw0 (hG.1.preconnected v w0)
  -- ... and it is the only one
  have honly : ∀ x, G.Adj v x → x = u := fun x hx =>
    (Set.ncard_le_one (s := G.neighborSet v) (Set.toFinite _)).1 (by omega) x hx u hu
  have hvu : v ≠ u := G.ne_of_adj hu
  -- a third vertex `w`
  obtain ⟨w, hwu, hwv⟩ : ∃ w, w ≠ u ∧ w ≠ v := by
    have hv_mem : v ∈ univ.erase u := mem_erase.2 ⟨hvu, mem_univ v⟩
    have hc : 0 < ((univ.erase u).erase v).card := by
      rw [card_erase_of_mem hv_mem, card_erase_of_mem (mem_univ u), card_univ]
      omega
    obtain ⟨w, hw⟩ := card_pos.1 hc
    rw [mem_erase, mem_erase] at hw
    exact ⟨w, hw.2.1, hw.1⟩
  -- deleting `u` isolates `v` from `w`
  have hvS : v ∈ ((↑({u} : Finset V) : Set V)ᶜ) := by simp [hvu]
  have hwS : w ∈ ((↑({u} : Finset V) : Set V)ᶜ) := by simp [hwu]
  have hnoadj : ∀ x : ↥((↑({u} : Finset V) : Set V)ᶜ),
      ¬ (G.induce ((↑({u} : Finset V) : Set V)ᶜ)).Adj ⟨v, hvS⟩ x := by
    intro x hx
    have hx' : G.Adj v x.1 := by simpa using hx
    exact x.2 (by simp [honly _ hx'])
  have hstuck : ∀ a b (p : (G.induce ((↑({u} : Finset V) : Set V)ᶜ)).Walk a b),
      a = ⟨v, hvS⟩ → b = ⟨v, hvS⟩ := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ _ =>
      intro ha
      subst ha
      exact absurd h (hnoadj _)
  have hne : (G.induce ((↑({u} : Finset V) : Set V)ᶜ)).connectedComponentMk ⟨v, hvS⟩
      ≠ (G.induce ((↑({u} : Finset V) : Set V)ᶜ)).connectedComponentMk ⟨w, hwS⟩ := by
    rw [Ne, ConnectedComponent.eq]
    rintro ⟨p⟩
    have := hstuck _ _ p rfl
    exact hwv (congrArg Subtype.val this)
  have h2 : 2 ≤ numComp G {u} := by
    unfold numComp
    haveI : Nontrivial (G.induce ((↑({u} : Finset V) : Set V)ᶜ)).ConnectedComponent :=
      ⟨⟨_, _, hne⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 this
  have := hG.2 {u} h2
  rw [card_singleton] at this
  omega
