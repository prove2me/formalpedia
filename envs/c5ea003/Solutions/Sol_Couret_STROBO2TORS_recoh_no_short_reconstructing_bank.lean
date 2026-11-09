-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_no_short_reconstructing_bank
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:27:05.436203+00:00
-- url     : https://prove2.me/submissions/855d09c5-e1f6-4f75-8e2a-479a5dd2967e

import Aesop
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paired_support_card_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_short_complex_character_bank_collision
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_torsion_subgroup_nsmul
import Definitions.Def_Couret_RecohBinaryLinearTransport_ea1ab9036ae4
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Definitions.Def_Couret_RecohPrimaryCharacters_3b850762e03a

set_option autoImplicit false

/-!
RECOH lower bound for the fixed labelled observation model.

The torsion groups are the actual subgroups G[2] and G[3]. Complex
character encodings are supplied by RecohComplexCharacterEncodings.
The sole size condition |G| >= 3 supplies a genuine three-point support.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

private theorem recoh_observation_eq_of_triple_probes
    {k : ℕ} (bank : Fin k → AddChar G ℂ)
    (a b c x y z : G)
    (hA : ({a, b, c} : Finset G).card = 3)
    (hB : ({x, y, z} : Finset G).card = 3)
    (hsq : ∀ q : G,
      orderedSquare ({a, b, c} : Finset G) q =
        orderedSquare ({x, y, z} : Finset G) q)
    (hprobe : ∀ i : Fin k,
      recohTripleProbe (bank i) a b c = recohTripleProbe (bank i) x y z) :
    recohObservation bank ({a, b, c} : Finset G) =
      recohObservation bank ({x, y, z} : Finset G) := by
  obtain ⟨hab, hac, hbc⟩ := displayed_three_distinct a b c hA
  obtain ⟨hxy, hxz, hyz⟩ := displayed_three_distinct x y z hB
  apply Prod.ext
  · funext q
    exact hsq q
  · funext i
    change recohSupportProbe (bank i) {a, b, c} =
      recohSupportProbe (bank i) {x, y, z}
    rw [recoh_support_probe_three (bank i) a b c hab hac hbc,
      recoh_support_probe_three (bank i) x y z hxy hxz hyz]
    exact hprobe i

/-- Every fixed complex-character bank shorter than the combined binary
and ternary torsion ranks fails to reconstruct all three-point supports.
The convolution square and the additional Fourier observations are labelled. -/
theorem p2m_local_recoh_no_short_reconstructing_bank [Fintype G]
    (r s k : ℕ) (hr : 0 < r) (hk : k < r + s)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s)
    (hG3 : 3 ≤ Fintype.card G) (bank : Fin k → AddChar G ℂ) :
    ¬ Function.Injective (fun S : {S : Finset G // S.card = 3} =>
      recohObservation bank S.1) := by
  classical
  intro hinj
  have hcollision (a b c x y z : G)
      (hA : ({a, b, c} : Finset G).card = 3)
      (hB : ({x, y, z} : Finset G).card = 3)
      (hne : ({a, b, c} : Finset G) ≠ {x, y, z})
      (hsq : ∀ q : G,
        orderedSquare ({a, b, c} : Finset G) q =
          orderedSquare ({x, y, z} : Finset G) q)
      (hprobe : ∀ i : Fin k,
        recohTripleProbe (bank i) a b c = recohTripleProbe (bank i) x y z) :
      False := by
    have hobs := recoh_observation_eq_of_triple_probes bank a b c x y z
      hA hB hsq hprobe
    have hsub : (⟨{a, b, c}, hA⟩ : {S : Finset G // S.card = 3}) =
        ⟨{x, y, z}, hB⟩ := hinj hobs
    exact hne (congrArg Subtype.val hsub)
  let H := recohTorsionSubgroup (G := G) 2
  let V := recohTorsionSubgroup (G := G) 3
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype V := Fintype.ofFinite V
  have hH : Fintype.card H = 2 ^ r := by
    simpa only [Nat.card_eq_fintype_card] using hcard2
  have hV : Fintype.card V = 3 ^ s := by
    simpa only [Nat.card_eq_fintype_card] using hcard3
  have h2 : ∀ a : H, a + a = 0 := by
    intro a
    simpa only [two_nsmul] using recoh_torsion_subgroup_nsmul (G := G) 2 a
  have h3 : ∀ a : V, (a + a) + a = 0 := by
    intro a
    have ha := recoh_torsion_subgroup_nsmul (G := G) 3 a
    change (2 + 1 : ℕ) • a = 0 at ha
    simpa only [add_nsmul, two_nsmul, one_nsmul] using ha
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset G)) (n := 3) (by simpa using hG3)
  obtain ⟨x, y, z, _, _, _, hdisplay⟩ := Finset.card_eq_three.mp hS
  have htriple : ({x, y, z} : Finset G).card = 3 := by
    simpa only [hdisplay] using hS
  obtain htranslation | hreflection :=
    recoh_short_complex_character_bank_collision r s k hr hk hV hH h2 h3
      (recohTorsionSubgroup (G := G) 2).subtype Subtype.val_injective
      (recohTorsionSubgroup (G := G) 3).subtype Subtype.val_injective
      bank x y z htriple
  · obtain ⟨d, _, _, hne, hsq, hprobe⟩ := htranslation
    have hT : ({x + d, y + d, z + d} : Finset G).card = 3 := by
      simpa only [translateSupport_three, htriple] using
        translateSupport_card ({x, y, z} : Finset G) d
    exact hcollision x y z (x + d) (y + d) (z + d) htriple hT hne hsq hprobe
  · obtain ⟨d, v, hd0, hd2, hv0, hv3, hne, hsq, hprobe⟩ := hreflection
    have hv2 : v + v ≠ 0 := by
      intro hv2
      apply hv0
      simpa only [hv2, zero_add] using hv3
    have hpos : (0 : G) + 0 ≠ v + v := by
      simpa only [zero_add] using hv2.symm
    have hneg : (0 : G) + 0 ≠ (-v) + (-v) := by
      intro h
      apply hv2
      have hh := congrArg (fun w : G => -w) h
      simpa only [neg_add_rev, neg_neg, neg_zero, zero_add] using hh.symm
    exact hcollision 0 v (v + d) 0 (-v) (-v + d)
      (paired_support_card_three 0 v d hd2 hd0 hpos)
      (paired_support_card_three 0 (-v) d hd2 hd0 hneg) hne hsq hprobe

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r s k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat k (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r s) →
      @Eq.{1} Nat
          (Nat.card.{p2m_u_0}
            (@Subtype.{p2m_u_0 + 1} G fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
        @Eq.{1} Nat
            (Nat.card.{p2m_u_0}
              (@Subtype.{p2m_u_0 + 1} G fun x =>
                @Membership.mem.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                    (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  x))
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) s) →
          @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
              (@Fintype.card.{p2m_u_0} G inst_2) →
            ∀
              (bank :
                Fin k →
                  @AddChar.{p2m_u_0, 0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
              Not
                (@Function.Injective.{p2m_u_0 + 1, p2m_u_0 + 1}
                  (@Subtype.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
                    @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (Prod.{p2m_u_0, 0} (G → Nat) (Fin k → Complex)) fun S =>
                  @Couret.STROBO2TORS.recohObservation.{p2m_u_0, 0} G inst inst_1 (Fin k) bank
                    (@Subtype.val.{p2m_u_0 + 1} (Finset.{p2m_u_0} G)
                      (fun S =>
                        @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      S)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_no_short_reconstructing_bank

