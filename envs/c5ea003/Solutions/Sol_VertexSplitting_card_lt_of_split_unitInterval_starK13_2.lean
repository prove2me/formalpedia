-- Prove2me | solution 2 for VertexSplitting.card_lt_of_split_unitInterval_starK13
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:57:09.669974+00:00
-- url     : https://prove2.me/submissions/9398c036-1433-4a2e-a72f-4b0b7488d5cf

import Mathlib
import Definitions.Def_Bridges_VertexSplitting
open VertexSplitting in
theorem solution {W : Type*} [Fintype W] {H : SimpleGraph W} {f : W → Fin 4}
    (h : IsSplit starK13 H f) (hH : HasUnitIntervalRep H) : 4 < Fintype.card W := by
  -- unit interval graphs are claw-free: three leaves pairwise `> 1` apart cannot all lie within `1`
  have hclawfree : ∀ a b c d : W, H.Adj a b → H.Adj a c → H.Adj a d → b ≠ c → b ≠ d → c ≠ d →
      ¬ H.Adj b c → ¬ H.Adj b d → ¬ H.Adj c d → False := by
    obtain ⟨p, hp⟩ := hH
    intro a b c d hab hac had hbc hbd hcd nbc nbd ncd
    have h1 := ((hp a b).1 hab).2
    have h2 := ((hp a c).1 hac).2
    have h3 := ((hp a d).1 had).2
    have n1 : 1 < |p b - p c| := by
      by_contra hh
      exact nbc ((hp b c).2 ⟨hbc, le_of_not_gt hh⟩)
    have n2 : 1 < |p b - p d| := by
      by_contra hh
      exact nbd ((hp b d).2 ⟨hbd, le_of_not_gt hh⟩)
    have n3 : 1 < |p c - p d| := by
      by_contra hh
      exact ncd ((hp c d).2 ⟨hcd, le_of_not_gt hh⟩)
    rw [abs_le] at h1 h2 h3
    rw [lt_abs] at n1 n2 n3
    rcases n1 with n1 | n1 <;> rcases n2 with n2 | n2 <;> rcases n3 with n3 | n3 <;>
      linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  by_contra hlt
  replace hlt := le_of_not_gt hlt
  have hcard := Fintype.card_le_of_surjective f h.surj
  rw [Fintype.card_fin] at hcard
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨h.surj, by rw [Fintype.card_fin]; omega⟩
  have hadj : ∀ x y, H.Adj x y ↔ starK13.Adj (f x) (f y) := by
    intro x y
    refine ⟨h.adj_proj x y, fun hxy => ?_⟩
    obtain ⟨x', y', hx', hy', hH'⟩ := h.cover _ _ hxy
    rwa [hbij.1 hx', hbij.1 hy'] at hH'
  -- `starK13` is itself a claw, so `H` would contain one
  obtain ⟨a, ha⟩ := h.surj 0
  obtain ⟨b, hb⟩ := h.surj 1
  obtain ⟨c, hc⟩ := h.surj 2
  obtain ⟨d, hd⟩ := h.surj 3
  refine hclawfree a b c d ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hadj, ha, hb]; decide
  · rw [hadj, ha, hc]; decide
  · rw [hadj, ha, hd]; decide
  · intro e; have := congrArg f e; rw [hb, hc] at this; exact absurd this (by decide)
  · intro e; have := congrArg f e; rw [hb, hd] at this; exact absurd this (by decide)
  · intro e; have := congrArg f e; rw [hc, hd] at this; exact absurd this (by decide)
  · rw [hadj, hb, hc]; decide
  · rw [hadj, hb, hd]; decide
  · rw [hadj, hc, hd]; decide
