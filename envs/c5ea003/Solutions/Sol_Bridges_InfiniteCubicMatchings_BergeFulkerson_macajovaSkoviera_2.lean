-- Prove2me | solution 2 for Bridges.InfiniteCubicMatchings.BergeFulkerson.macajovaSkoviera
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:11:11.999662+00:00
-- url     : https://prove2.me/submissions/d5d9b0d0-2b60-40f9-819d-766bd5552b46

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
open Bridges.InfiniteCubicMatchings in
theorem solution {V : Type*} {G : SimpleGraph V} (h : BergeFulkerson G) :
    MacajovaSkoviera G := by
  classical
  -- parity: a finite set closed under a perfect matching has even size
  have hpar : ∀ (M : PerfectMatching G) (n : ℕ) (S : Finset V), S.card = n →
      (∀ v ∈ S, M.partner v ∈ S) → Even n := by
    intro M n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hcl
      rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · rw [← hS]
        simp
      · have hne : M.partner v ≠ v := (G.ne_of_adj (M.isAdj v)).symm
        have hmem : M.partner v ∈ S.erase v := Finset.mem_erase.mpr ⟨hne, hcl v hv⟩
        have h2 : 1 < S.card := Finset.one_lt_card.mpr ⟨v, hv, M.partner v, hcl v hv, hne.symm⟩
        have hcard : ((S.erase v).erase (M.partner v)).card = n - 2 := by
          rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem hv, hS]
          omega
        have hcl' : ∀ x ∈ (S.erase v).erase (M.partner v),
            M.partner x ∈ (S.erase v).erase (M.partner v) := by
          intro x hx
          simp only [Finset.mem_erase] at hx ⊢
          refine ⟨fun hx' => hx.2.1 ?_, fun hx' => hx.1 ?_, hcl x hx.2.2⟩
          · rw [← M.invol x, hx', M.invol v]
          · rw [← M.invol x, hx']
        obtain ⟨k, hk⟩ := ih (n - 2) (by omega) _ hcard hcl'
        exact ⟨k + 1, by omega⟩
  obtain ⟨M, hM⟩ := h
  refine ⟨M 0, M 1, ?_⟩
  rintro C ⟨S, hodd, rfl⟩ hsub
  -- the third matching crosses the odd cut
  obtain ⟨v, hv, hout⟩ : ∃ v ∈ S, (M 2).partner v ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact (Nat.not_even_iff_odd.mpr hodd) (hpar (M 2) S.card S rfl hcon)
  have he : s(v, (M 2).partner v) ∈ G.edgeSet := (M 2).isAdj v
  have hcut : s(v, (M 2).partner v) ∈ cutEdges G S := ⟨he, v, (M 2).partner v, rfl, hv, hout⟩
  have h01 := hsub hcut
  -- so that edge lies in three of the six matchings
  have hthree : 2 < {i : Fin 6 | s(v, (M 2).partner v) ∈ (M i).edges}.ncard := by
    rw [Set.two_lt_ncard_iff (Set.toFinite _)]
    exact ⟨0, 1, 2, h01.1, h01.2, ⟨v, rfl⟩, by decide, by decide, by decide⟩
  rw [hM _ he] at hthree
  exact lt_irrefl 2 hthree
