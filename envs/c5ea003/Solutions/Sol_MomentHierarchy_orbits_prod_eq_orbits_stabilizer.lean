-- Prove2me | solution 1 for MomentHierarchy.orbits_prod_eq_orbits_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T04:51:45.731056+00:00
-- url     : https://prove2.me/submissions/9dd81950-b4ce-4c90-b85f-ae4a8741e6f9

import Definitions.Def_Logic_MomentHierarchy

open MulAction

universe u v

open MulAction in
/-- **Orbits on pairs are suborbits**: for a transitive action, `G`-orbits on `X × X`
correspond to `Stab(x₀)`-orbits on `X`. -/
theorem solution {G : Type u} {X : Type v} [Group G] [MulAction G X] (x0 : X)
    (htrans : IsPretransitive G X) :
    Nat.card (orbitRel.Quotient G (X × X)) = Nat.card (orbitRel.Quotient (stabilizer G x0) X) := by
  haveI := htrans
  classical
  let c : X → G := fun a => (exists_smul_eq G a x0).choose
  have hc : ∀ a, c a • a = x0 := fun a => (exists_smul_eq G a x0).choose_spec
  have wd1 : ∀ p q : X × X, orbitRel G (X × X) p q →
      (Quotient.mk (orbitRel (stabilizer G x0) X) (c p.1 • p.2))
        = Quotient.mk (orbitRel (stabilizer G x0) X) (c q.1 • q.2) := by
    intro p q hpq
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hpq)
    obtain ⟨a, b⟩ := p
    obtain ⟨a', b'⟩ := q
    simp only [Prod.smul_mk, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    apply Quotient.sound
    refine mem_orbit_iff.mpr ⟨⟨c (k • a') * k * (c a')⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff.mpr (hc a').symm, hc]
    · simp only [Subgroup.smul_def, mul_smul, inv_smul_smul]
  have wd2 : ∀ y z : X, orbitRel (stabilizer G x0) X y z →
      (Quotient.mk (orbitRel G (X × X)) (x0, y)) = Quotient.mk (orbitRel G (X × X)) (x0, z) := by
    intro y z hyz
    obtain ⟨⟨h, hh⟩, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hyz)
    apply Quotient.sound
    refine mem_orbit_iff.mpr ⟨h, ?_⟩
    rw [mem_stabilizer_iff] at hh
    simp only [Subgroup.smul_def] at hk
    simp [Prod.smul_mk, hh, hk]
  refine Nat.card_congr
    { toFun := Quotient.lift (s := orbitRel G (X × X))
        (fun p : X × X => Quotient.mk (orbitRel (stabilizer G x0) X) (c p.1 • p.2)) wd1
      invFun := Quotient.lift (s := orbitRel (stabilizer G x0) X)
        (fun y : X => Quotient.mk (orbitRel G (X × X)) (x0, y)) wd2
      left_inv := fun q => Quotient.inductionOn q (fun p => ?_)
      right_inv := fun q => Quotient.inductionOn q (fun y => ?_) }
  · obtain ⟨a, b⟩ := p
    apply Quotient.sound
    exact mem_orbit_iff.mpr ⟨c a, by simp [Prod.smul_mk, hc a]⟩
  · apply Quotient.sound
    exact mem_orbit_iff.mpr ⟨⟨c x0, mem_stabilizer_iff.mpr (hc x0)⟩, rfl⟩
