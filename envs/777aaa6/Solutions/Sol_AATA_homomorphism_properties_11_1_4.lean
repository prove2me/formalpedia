-- Prove2me | solution 1 for AATA.homomorphism_properties_11_1_4
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:10:09.596096+00:00
-- url     : https://prove2.me/submissions/3eb842dd-6d79-43c1-9646-eff35b4ea6fb

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 200000
universe u v

theorem solution {G : Type u} {H : Type v} [Group G] [Group H] (f : G →* H) :
    f 1 = 1 ∧
    (∀ g : G, f g⁻¹ = (f g)⁻¹) ∧
    (∀ K : Subgroup G, ∃ L : Subgroup H, (L : Set H) = f '' (K : Set G)) ∧
    (∀ L : Subgroup H, ∃ K : Subgroup G,
      (K : Set G) = f ⁻¹' (L : Set H) ∧ (L.Normal → K.Normal)) := by
  refine ⟨f.map_one, fun g => f.map_inv g, ?_, ?_⟩
  · intro K
    exact ⟨K.map f, rfl⟩
  · intro L
    exact ⟨L.comap f, rfl, fun h => h.comap f⟩
