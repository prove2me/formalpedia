-- Prove2me | solution 2 for Bridges.InfiniteCubicMatchings.k4Chain_macajovaSkoviera
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:06:38.119238+00:00
-- url     : https://prove2.me/submissions/cd234a80-0cdd-4f79-adce-653d321930a5

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsPetersenLift
open Bridges.InfiniteCubicMatchings in
theorem solution : MacajovaSkoviera k4Chain := by
  classical
  -- lift the three perfect matchings of `K₄` along the voltage
  have hinv : ∀ (i : Fin 3) (u : Fin 4), k4PM i (k4PM i u) = u := by decide
  have hvol : ∀ (i : Fin 3) (u : Fin 4), k4Vol u (k4PM i u) + k4Vol (k4PM i u) (k4PM i (k4PM i u)) = 0 := by
    decide
  let L : Fin 3 → PerfectMatching k4Chain := fun i =>
    { partner := fun p => (p.1 + k4Vol p.2 (k4PM i p.2), k4PM i p.2)
      isAdj := fun p => ⟨(k4Matching i).isAdj p.2, rfl⟩
      invol := fun p => by
        refine Prod.ext ?_ (hinv i p.2)
        simp only
        rw [add_assoc, hvol i p.2, add_zero] }
  -- lifts of different colour classes share no edge (project to `K₄`)
  have hdisj : ∀ e, e ∈ (L 0).edges → e ∉ (L 1).edges := by
    rintro e ⟨p, rfl⟩ ⟨q, hq⟩
    have h1 := congrArg (Sym2.map Prod.snd) hq
    simp only [Sym2.map_mk, L] at h1
    have key : ∀ u w : Fin 4, s(u, k4PM 0 u) ≠ s(w, k4PM 1 w) := by decide
    exact key _ _ h1
  -- parity: a finite set closed under a perfect matching has even size
  have hpar : ∀ (M : PerfectMatching k4Chain) (n : ℕ) (S : Finset (ℤ × Fin 4)), S.card = n →
      (∀ v ∈ S, M.partner v ∈ S) → Even n := by
    intro M n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S hS hcl
      rcases S.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
      · rw [← hS]
        simp
      · have hne : M.partner v ≠ v := (k4Chain.ne_of_adj (M.isAdj v)).symm
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
  refine ⟨L 0, L 1, ?_⟩
  rintro C ⟨S, hodd, rfl⟩ hsub
  -- the first lifted matching crosses the odd cut, but that edge is not in the second
  obtain ⟨v, hv, hout⟩ : ∃ v ∈ S, (L 0).partner v ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact (Nat.not_even_iff_odd.mpr hodd) (hpar (L 0) S.card S rfl hcon)
  have he : s(v, (L 0).partner v) ∈ k4Chain.edgeSet := (L 0).isAdj v
  have hcut : s(v, (L 0).partner v) ∈ cutEdges k4Chain S := ⟨he, v, (L 0).partner v, rfl, hv, hout⟩
  exact hdisj _ ⟨v, rfl⟩ (hsub hcut).2
