-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.orbitRel_prod_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:01:47.316128+00:00
-- url     : https://prove2.me/submissions/ed67b2cd-b5a0-4d93-b165-22ea7d1351ca

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity
open Catalog.Novelty.OrbitalRigidity in
theorem solution {G X : Type*} [Group G] [MulAction G X] :
    (∀ x y x' y' : X, ((∃ g : G, g • x = x') ∧ (∃ g : G, g • y = y')) ↔
        (∃ g : G, g • x = x' ∧ g • y = y')) ↔ ActsTrivially G X := by
  constructor
  · -- test the pair `(x, x) ↦ (g • x, x)`: a common mover must fix `x` and send it to `g • x`
    intro h g x
    obtain ⟨k, hk1, hk2⟩ := (h x x (g • x) x).mp ⟨⟨g, rfl⟩, ⟨1, one_smul G x⟩⟩
    rw [← hk1, hk2]
  · -- a trivial action moves nothing, so both sides say `x = x' ∧ y = y'`
    intro htriv x y x' y'
    constructor
    · rintro ⟨⟨g, hg⟩, ⟨g', hg'⟩⟩
      refine ⟨1, ?_, ?_⟩
      · rw [one_smul, ← hg, htriv]
      · rw [one_smul, ← hg', htriv]
    · rintro ⟨g, hg, hg'⟩
      exact ⟨⟨g, hg⟩, ⟨g, hg'⟩⟩
