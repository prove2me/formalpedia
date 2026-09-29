-- Prove2me | solution 1 for FanoStrongBlocking.fano_strongBlocking_iff_six
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T02:05:50.094326+00:00
-- url     : https://prove2.me/submissions/91133560-de83-4c9b-9fb5-23f5d059dc67

import Mathlib
import Definitions.Def_Geometry_FanoStrongBlocking_Core
open FanoStrongBlocking Finset in
theorem solution {S : Finset V} (hS : S ⊆ Pts) : StrongBlocking S ↔ 6 ≤ S.card := by
  have h7 : Pts.card = 7 := by decide
  have hsd : (Pts \ S).card = 7 - S.card := by rw [card_sdiff_of_subset hS, h7]
  have hSle : S.card ≤ 7 := h7 ▸ card_le_card hS
  have hchar : ∀ v : V, v + v = 0 := by decide
  have hmem : ∀ v : V, v ≠ 0 → v ∈ Pts := fun v hv => mem_filter.mpr ⟨mem_univ _, hv⟩
  constructor
  · -- two missing points `p ≠ q` starve the line `{p, q, p + q}`
    intro hB
    by_contra hlt
    push_neg at hlt
    have h2 : 1 < (Pts \ S).card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp h2
    rw [mem_sdiff] at hp hq
    have hp0 : p ≠ 0 := (mem_filter.mp hp.1).2
    have hq0 : q ≠ 0 := (mem_filter.mp hq.1).2
    have hsum0 : p + q ≠ 0 := by
      intro h
      apply hpq
      calc p = p + (q + q) := by rw [hchar, add_zero]
        _ = (p + q) + q := by abel
        _ = q := by rw [h, zero_add]
    have hline : IsLine p q (p + q) :=
      ⟨hp0, hq0, hsum0, hpq, fun h => hq0 (by simpa using h), fun h => hp0 (by simpa using h),
        hchar _⟩
    rcases hB p q (p + q) hline with h | h | h
    · exact hp.2 h.1
    · exact hp.2 h.1
    · exact hq.2 h.1
  · -- a starved line has two missing points, forcing `|S| ≤ 5`
    intro h6 a b c hl
    obtain ⟨ha0, hb0, hc0, hab, hac, hbc, -⟩ := hl
    by_contra hcon
    push_neg at hcon
    have key : ∃ p q, p ≠ q ∧ p ∈ Pts \ S ∧ q ∈ Pts \ S := by
      by_cases ha : a ∈ S
      · exact ⟨b, c, hbc, mem_sdiff.mpr ⟨hmem b hb0, hcon.1 ha⟩,
          mem_sdiff.mpr ⟨hmem c hc0, hcon.2.1 ha⟩⟩
      · by_cases hb : b ∈ S
        · exact ⟨a, c, hac, mem_sdiff.mpr ⟨hmem a ha0, ha⟩,
            mem_sdiff.mpr ⟨hmem c hc0, hcon.2.2 hb⟩⟩
        · exact ⟨a, b, hab, mem_sdiff.mpr ⟨hmem a ha0, ha⟩, mem_sdiff.mpr ⟨hmem b hb0, hb⟩⟩
    obtain ⟨p, q, hpq, hp, hq⟩ := key
    have : 1 < (Pts \ S).card := one_lt_card.mpr ⟨p, hp, q, hq, hpq⟩
    omega
