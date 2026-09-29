-- Prove2me | solution 1 for VertexSplitting.hasInducedClaw_of_split_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T20:05:23.643398+00:00
-- url     : https://prove2.me/submissions/04eb71bf-970a-4a2b-9286-b33c7e562415

import Mathlib
import Definitions.Def_Bridges_VertexSplitting
open VertexSplitting in
theorem solution {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {f : W → V}
    (h : IsSplit G H f) (hf : Function.Injective f) (hG : HasInducedClaw G) :
    HasInducedClaw H := by
  -- an injective splitting is an isomorphism onto `G`
  have hadj : ∀ x y, H.Adj x y ↔ G.Adj (f x) (f y) := by
    intro x y
    refine ⟨h.adj_proj x y, fun hxy => ?_⟩
    obtain ⟨x', y', hx', hy', hH⟩ := h.cover _ _ hxy
    rwa [hf hx', hf hy'] at hH
  -- pull the claw back along the surjection
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, nbc, nbd, ncd⟩ := hG
  obtain ⟨a', rfl⟩ := h.surj a
  obtain ⟨b', rfl⟩ := h.surj b
  obtain ⟨c', rfl⟩ := h.surj c
  obtain ⟨d', rfl⟩ := h.surj d
  exact ⟨a', b', c', d', (hadj _ _).2 hab, (hadj _ _).2 hac, (hadj _ _).2 had,
    fun e => hbc (congrArg f e), fun e => hbd (congrArg f e), fun e => hcd (congrArg f e),
    fun e => nbc ((hadj _ _).1 e), fun e => nbd ((hadj _ _).1 e), fun e => ncd ((hadj _ _).1 e)⟩
