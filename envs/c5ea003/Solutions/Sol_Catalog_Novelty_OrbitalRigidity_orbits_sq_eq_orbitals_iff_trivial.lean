-- Prove2me | solution 1 for Catalog.Novelty.OrbitalRigidity.orbits_sq_eq_orbitals_iff_trivial
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:56:36.897319+00:00
-- url     : https://prove2.me/submissions/28be5762-fde3-4634-a6fd-bb1fdb10a4e1

import Mathlib
import Definitions.Def_Novelty_OrbitalRigidity

open Catalog.Novelty.OrbitalRigidity MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem solution :
    (∀ x y : X, orbit G ((x, y) : X × X) = (orbit G x) ×ˢ (orbit G y)) ↔
      ActsTrivially G X := by
  constructor
  · intro h g x
    have hx := h x x
    have hxorb : x ∈ orbit G x := mem_orbit_self x
    have hgorb : g • x ∈ orbit G x := mem_orbit x g
    have hprod : (g • x, x) ∈ (orbit G x) ×ˢ (orbit G x) :=
      Set.mem_prod.mpr ⟨hgorb, hxorb⟩
    have horb : (g • x, x) ∈ orbit G (x, x) := hx ▸ hprod
    rw [mem_orbit_iff] at horb
    obtain ⟨h', hh'⟩ := horb
    -- hh' : h' • (x, x) = (g • x, x)
    have h1 : h' • x = g • x := congrArg Prod.fst hh'
    have h2 : h' • x = x := congrArg Prod.snd hh'
    exact h1.symm.trans h2
  · intro htriv x y
    ext p
    constructor
    · intro hp
      rw [mem_orbit_iff] at hp
      obtain ⟨g, rfl⟩ := hp
      exact Set.mem_prod.mpr ⟨mem_orbit x g, mem_orbit y g⟩
    · intro hp
      obtain ⟨hx', hy'⟩ := Set.mem_prod.mp hp
      rw [mem_orbit_iff] at hx' hy'
      obtain ⟨g, hg⟩ := hx'
      obtain ⟨g', hg'⟩ := hy'
      -- p = (g•x, g'•y); under trivial action both equal (x,y)
      have hxeq : g • x = x := htriv g x
      have hyeq : g' • y = y := htriv g' y
      have hpxy : p = (x, y) := by
        apply Prod.ext
        · rw [← hg, hxeq]
        · rw [← hg', hyeq]
      rw [hpxy]
      exact mem_orbit_self (x, y)
