-- Prove2me | solution 1 for GaloisTopologyBridge.continuous_upperAlexandrov_iff_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:23.43647+00:00
-- url     : https://prove2.me/submissions/d361f834-fce6-4d69-88cc-e14c8766d322

-- Sol generated from Bridges/GaloisTopologyBridge.lean
import Mathlib
import Definitions.Def_Bridges_GaloisTopologyBridge

open Set Topology

open GaloisTopologyBridge







variable {R : Type*} [CommRing R]






open Classical






open GaloisTopologyBridge in
theorem solution    {α β : Type*} [Preorder α] [Preorder β] (f : α → β) :
    @Continuous α β (upperAlexandrov α) (upperAlexandrov β) f ↔ Monotone f := by
  constructor
  · intro hf a b hab
    rw [continuous_def] at hf
    have hopen := hf {y | f a ≤ y} (fun x y hxy hx => le_trans hx hxy)
    have ha_mem : a ∈ f ⁻¹' {y | f a ≤ y} := by simp
    have hb_mem := hopen hab ha_mem
    simpa using hb_mem
  · intro hf
    rw [continuous_def]
    intro s hs x y hxy hfx
    exact hs (hf hxy) hfx
