-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.multiCopies_macajovaSkoviera
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:34:31.304675+00:00
-- url     : https://prove2.me/submissions/7d65cccb-f21b-4996-a0b7-6ae98a378eb7

import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
open Bridges.InfiniteCubicMatchings in
theorem solution {W : Type*} {ι : Type*} {K : SimpleGraph W}
    (h : MacajovaSkoviera K) : MacajovaSkoviera (multiCopies ι K) := by
  classical
  obtain ⟨M₁, M₂, hM⟩ := h
  -- copy a matching of `K` into every component
  let lift : PerfectMatching K → PerfectMatching (multiCopies ι K) := fun M =>
    { partner := fun p => (p.1, M.partner p.2)
      isAdj := fun p => ⟨rfl, M.isAdj p.2⟩
      invol := fun p => Prod.ext rfl (M.invol p.2) }
  have hproj : ∀ (M : PerfectMatching K) (j : ι) (a b : W),
      s((j, a), (j, b)) ∈ (lift M).edges → s(a, b) ∈ M.edges := by
    rintro M j a b ⟨p, hp⟩
    refine ⟨p.2, ?_⟩
    have := congrArg (Sym2.map Prod.snd) hp
    simpa [Sym2.map_mk, lift] using this
  refine ⟨lift M₁, lift M₂, ?_⟩
  rintro C ⟨S, hodd, rfl⟩ hsub
  -- some copy meets `S` in an odd number of vertices
  obtain ⟨j, hj⟩ : ∃ j : ι, Odd (S.filter (fun p : ι × W => p.1 = j)).card := by
    by_contra hcon
    push_neg at hcon
    have heven : Even S.card := by
      rw [Finset.card_eq_sum_card_image Prod.fst S]
      exact Finset.even_sum _ (fun j _ => Nat.not_odd_iff_even.mp (hcon j))
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  set T : Finset W := (S.filter (fun p : ι × W => p.1 = j)).image Prod.snd with hTdef
  have hT : ∀ a, a ∈ T ↔ (j, a) ∈ S := by
    intro a
    simp only [hTdef, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨k, b⟩, ⟨hk, hkj⟩, hba⟩
      simp only at hkj hba
      subst hkj
      subst hba
      exact hk
    · intro ha
      exact ⟨(j, a), ⟨ha, rfl⟩, rfl⟩
  have hTcard : T.card = (S.filter (fun p : ι × W => p.1 = j)).card := by
    apply Finset.card_image_of_injOn
    rintro ⟨k, a⟩ hka ⟨k', a'⟩ hka' hh
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hka hka'
    simp only at hh
    exact Prod.ext (hka.2.trans hka'.2.symm) hh
  -- the cut of that slice would be an odd cut of `K` inside `M₁ ∩ M₂`
  apply hM (cutEdges K T) ⟨T, by rw [hTcard]; exact hj, rfl⟩
  rintro e ⟨he, a, b, rfl, ha, hb⟩
  have hab : K.Adj a b := he
  have hcut : s((j, a), (j, b)) ∈ cutEdges (multiCopies ι K) S :=
    ⟨⟨rfl, hab⟩, (j, a), (j, b), rfl, (hT a).mp ha, fun hb' => hb ((hT b).mpr hb')⟩
  exact ⟨hproj M₁ j a b (hsub hcut).1, hproj M₂ j a b (hsub hcut).2⟩
