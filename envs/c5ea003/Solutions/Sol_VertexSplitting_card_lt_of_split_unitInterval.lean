-- Prove2me | solution 1 for VertexSplitting.card_lt_of_split_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T21:06:34.635979+00:00
-- url     : https://prove2.me/submissions/b0c416a2-7303-4af0-a474-21297b350ef6

import Mathlib
import Definitions.Def_Bridges_VertexSplitting
open VertexSplitting in
theorem solution {V W : Type*} [Fintype V] [Fintype W] {G : SimpleGraph V}
    {H : SimpleGraph W} {f : W → V} (h : IsSplit G H f) (hH : HasUnitIntervalRep H)
    (hG : HasInducedClaw G) : Fintype.card V < Fintype.card W := by
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
  -- equal sizes force the splitting to be a bijection, hence an isomorphism
  have hcard := Fintype.card_le_of_surjective f h.surj
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).2 ⟨h.surj, by omega⟩
  have hadj : ∀ x y, H.Adj x y ↔ G.Adj (f x) (f y) := by
    intro x y
    refine ⟨h.adj_proj x y, fun hxy => ?_⟩
    obtain ⟨x', y', hx', hy', hH⟩ := h.cover _ _ hxy
    rwa [hbij.1 hx', hbij.1 hy'] at hH
  -- pull the claw of `G` back to `H`
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, nbc, nbd, ncd⟩ := hG
  obtain ⟨a', rfl⟩ := h.surj a
  obtain ⟨b', rfl⟩ := h.surj b
  obtain ⟨c', rfl⟩ := h.surj c
  obtain ⟨d', rfl⟩ := h.surj d
  exact hclawfree a' b' c' d' ((hadj _ _).2 hab) ((hadj _ _).2 hac) ((hadj _ _).2 had)
    (fun e => hbc (congrArg f e)) (fun e => hbd (congrArg f e)) (fun e => hcd (congrArg f e))
    (fun e => nbc ((hadj _ _).1 e)) (fun e => nbd ((hadj _ _).1 e)) (fun e => ncd ((hadj _ _).1 e))
