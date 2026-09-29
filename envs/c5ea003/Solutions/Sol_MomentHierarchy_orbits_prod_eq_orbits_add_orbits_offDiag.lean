-- Prove2me | solution 1 for MomentHierarchy.orbits_prod_eq_orbits_add_orbits_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T04:40:10.769469+00:00
-- url     : https://prove2.me/submissions/5d51377f-21b8-4434-9199-01e45690db99

import Definitions.Def_Logic_MomentHierarchy

open MulAction MomentHierarchy

universe u v

open MulAction MomentHierarchy in
/-- **Rank splitting**: orbits on `X × X` = orbits on `X` + orbits on the off-diagonal. -/
theorem solution {G : Type u} {X : Type v} [Group G] [Fintype G] [MulAction G X] [Finite X] :
    Nat.card (orbitRel.Quotient G (X × X))
      = Nat.card (orbitRel.Quotient G X)
        + Nat.card (orbitRel.Quotient G (offDiagSub G X)) := by
  classical
  have burn : ∀ (Y : Type v) [MulAction G Y] [Finite Y],
      ∑ g : G, Nat.card (fixedBy Y g) = Nat.card (orbitRel.Quotient G Y) * Nat.card G := by
    intro Y _ _
    haveI : Fintype Y := Fintype.ofFinite Y
    have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G Y
    simpa only [Nat.card_eq_fintype_card] using h
  have hprod : ∀ g : G,
      Nat.card (fixedBy (X × X) g) = Nat.card (fixedBy X g) * Nat.card (fixedBy X g) := by
    intro g
    rw [Nat.card_congr (fixedByProdEquiv g), Nat.card_prod]
  have hoff : ∀ g : G, Nat.card (fixedBy (offDiagSub G X) g)
      = Nat.card (fixedBy X g) * Nat.card (fixedBy X g) - Nat.card (fixedBy X g) := by
    intro g
    rw [Nat.card_congr (fixedByOffDiagEquiv g)]
    have hdiag : Nat.card {q : fixedBy X g × fixedBy X g // q.1 = q.2} = Nat.card (fixedBy X g) :=
      Nat.card_congr
        { toFun := fun q => q.1.1
          invFun := fun x => ⟨(x, x), rfl⟩
          left_inv := fun q => by
            obtain ⟨⟨a, b⟩, h⟩ := q
            simp only at h
            subst h
            rfl
          right_inv := fun x => rfl }
    have hsplit : Nat.card {q : fixedBy X g × fixedBy X g // q.1 = q.2}
        + Nat.card {q : fixedBy X g × fixedBy X g // ¬ q.1 = q.2}
        = Nat.card (fixedBy X g) * Nat.card (fixedBy X g) := by
      rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl _), Nat.card_prod]
    have hne : Nat.card {q : fixedBy X g × fixedBy X g // q.1 ≠ q.2}
        = Nat.card {q : fixedBy X g × fixedBy X g // ¬ q.1 = q.2} := rfl
    omega
  have hG : 0 < Nat.card G := Nat.card_pos
  have hXX := burn (X × X)
  have hX := burn X
  have hOD := burn (offDiagSub G X)
  simp only [hprod] at hXX
  simp only [hoff] at hOD
  have hsum : ∑ g : G, (Nat.card (fixedBy X g) * Nat.card (fixedBy X g))
      = ∑ g : G, (Nat.card (fixedBy X g) * Nat.card (fixedBy X g) - Nat.card (fixedBy X g))
        + ∑ g : G, Nat.card (fixedBy X g) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    have := Nat.le_mul_self (Nat.card (fixedBy X g))
    omega
  rw [hsum, hOD, hX, ← add_mul] at hXX
  have := Nat.eq_of_mul_eq_mul_right hG hXX
  omega
