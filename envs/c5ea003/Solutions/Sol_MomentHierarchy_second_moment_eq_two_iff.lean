-- Prove2me | solution 1 for MomentHierarchy.second_moment_eq_two_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T04:45:26.681586+00:00
-- url     : https://prove2.me/submissions/fb03cfdd-3dc5-4c9e-826f-b91bb763d78d

import Definitions.Def_Logic_MomentHierarchy

open MulAction MomentHierarchy

universe u v

open MulAction MomentHierarchy in
/-- **Spectral criterion**: transitive and 2-transitive iff the second moment is `2 |G|`. -/
theorem solution {G : Type u} {X : Type v} [Group G] [Fintype G] [MulAction G X] [Finite X]
    [Nontrivial X] :
    (IsPretransitive G X ∧ IsPretransitive G (offDiagSub G X))
      ↔ ∑ g : G, Nat.card (fixedBy X g) ^ 2 = 2 * Nat.card G := by
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
  have hG : 0 < Nat.card G := Nat.card_pos
  -- rank splitting (the accepted orbits_prod_eq_orbits_add_orbits_offDiag, inlined)
  have split : Nat.card (orbitRel.Quotient G (X × X))
      = Nat.card (orbitRel.Quotient G X) + Nat.card (orbitRel.Quotient G (offDiagSub G X)) := by
    have hoff : ∀ g : G, Nat.card (fixedBy (offDiagSub G X) g)
        = Nat.card (fixedBy X g) * Nat.card (fixedBy X g) - Nat.card (fixedBy X g) := by
      intro g
      rw [Nat.card_congr (fixedByOffDiagEquiv g)]
      have hdiag : Nat.card {q : fixedBy X g × fixedBy X g // q.1 = q.2}
          = Nat.card (fixedBy X g) :=
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
  have hsq : ∑ g : G, Nat.card (fixedBy X g) ^ 2
      = (Nat.card (orbitRel.Quotient G X) + Nat.card (orbitRel.Quotient G (offDiagSub G X)))
        * Nat.card G := by
    simp only [sq, ← hprod]
    rw [burn (X × X), split]
  haveI hneOD : Nonempty (offDiagSub G X) := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨⟨(x, y), hxy⟩⟩
  have one_iff : ∀ (Y : Type v) [MulAction G Y] [Finite Y] [Nonempty Y],
      IsPretransitive G Y ↔ Nat.card (orbitRel.Quotient G Y) = 1 := by
    intro Y _ _ _
    have hq : Nonempty (orbitRel.Quotient G Y) := ⟨Quotient.mk _ (Classical.arbitrary Y)⟩
    rw [MulAction.pretransitive_iff_subsingleton_quotient, Nat.card_eq_one_iff_unique]
    exact ⟨fun h => ⟨h, hq⟩, fun h => h.1⟩
  have pos : ∀ (Y : Type v) [MulAction G Y] [Finite Y] [Nonempty Y],
      1 ≤ Nat.card (orbitRel.Quotient G Y) := by
    intro Y _ _ _
    have hq : Nonempty (orbitRel.Quotient G Y) := ⟨Quotient.mk _ (Classical.arbitrary Y)⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨hq, inferInstance⟩)
  have h1 := pos X
  have h2 := pos (offDiagSub G X)
  rw [one_iff X, one_iff (offDiagSub G X), hsq]
  constructor
  · rintro ⟨ha, hb⟩
    rw [ha, hb]
  · intro h
    have h3 := Nat.eq_of_mul_eq_mul_right hG h
    exact ⟨by omega, by omega⟩
