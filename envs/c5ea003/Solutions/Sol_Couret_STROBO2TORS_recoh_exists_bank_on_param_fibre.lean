-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_bank_on_param_fibre
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:40.992722+00:00
-- url     : https://prove2.me/submissions/494193ac-0779-413e-bf59-63379f2a2f53

import Aesop
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
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
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_bank_injective_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_param_square_fibre_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_probe_constant_on_torsion_orbit
import Theorems.Thm_Couret_STROBO2TORS_recoh_third_probe_separates_exceptional
import Theorems.Thm_Couret_STROBO2TORS_recoh_three_primary_character_detects
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_characters_of_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_primary_support_probe_nonzero
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Mathlib.Data.Finite.Card

set_option autoImplicit false

/-!
Character banks chosen after the labelled ordered square has been observed.
The bank may depend on the complete square fibre, but is fixed on that fibre.
The ordinary fibre needs the two-torsion rank many character slots.  An
exceptional fibre needs at most one additional character slot, independently
of the three-torsion rank of the ambient finite abelian group.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











/-- The bank for the displayed exceptional fibre consists of the global
two-primary bank and one three-primary character selected for this fibre. -/
theorem p2m_local_recoh_exists_bank_on_param_fibre
    (r : ℕ)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (a d v : G) (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0) :
    ∃ bank : Fin (r + 1) → AddChar G ℂ,
      Set.InjOn (fun T : Finset G => fun i => recohSupportProbe (bank i) T)
        (squareFibre (paramSupport ((a, d), v))) := by
  classical
  obtain ⟨bank2, hprimary2, hsep2⟩ := recoh_two_primary_characters_of_card r hcard2
  obtain ⟨chi, _, htrivial, hdetect⟩ := recoh_three_primary_character_detects v hv hv0
  let bank : Fin (r + 1) → AddChar G ℂ :=
    Fin.addCases bank2 (fun _ : Fin 1 => chi)
  have hp3 := paramSupport_card a d v hd hd0 hv hv0
  have hq3 := paramSupport_card a d (-v) hd hd0
    (three_torsion_neg v hv) (neg_ne_zero.mpr hv0)
  have hP := recoh_bank_injective_on_torsion_orbit bank2 (paramSupport ((a, d), v))
    (fun i => recoh_two_primary_support_probe_nonzero (bank2 i) (hprimary2 i) _ hp3) hsep2
  have hQ := recoh_bank_injective_on_torsion_orbit bank2 (paramSupport ((a, d), -v))
    (fun i => recoh_two_primary_support_probe_nonzero (bank2 i) (hprimary2 i) _ hq3) hsep2
  have hneq : recohSupportProbe chi (paramSupport ((a, d), v)) ≠
      recohSupportProbe chi (paramSupport ((a, d), -v)) := by
    simpa [translateSupport] using
      (recoh_third_probe_separates_exceptional chi a d v 0 hd hd0 hv hv0
        (htrivial d hd) chi.map_zero_eq_one hdetect)
  refine ⟨bank, ?_⟩
  rw [recoh_param_square_fibre_eq a d v hd hd0 hv hv0]
  intro T hT U hU heq
  have heq2 : (fun i => recohSupportProbe (bank2 i) T) =
      (fun i => recohSupportProbe (bank2 i) U) := by
    funext i
    have h := congrFun heq (Fin.castAdd 1 i)
    simpa only [bank, Fin.addCases_left] using h
  have heq3 : recohSupportProbe chi T = recohSupportProbe chi U := by
    have h := congrFun heq (Fin.natAdd r (0 : Fin 1))
    simpa only [bank, Fin.addCases_right] using h
  rcases Finset.mem_union.mp hT with hT | hT
  · rcases Finset.mem_union.mp hU with hU | hU
    · exact hP hT hU heq2
    · exact (hneq (by
        calc
          recohSupportProbe chi (paramSupport ((a, d), v)) =
              recohSupportProbe chi T :=
            (recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hT).symm
          _ = recohSupportProbe chi U := heq3
          _ = recohSupportProbe chi (paramSupport ((a, d), -v)) :=
            recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hU)).elim
  · rcases Finset.mem_union.mp hU with hU | hU
    · exact (hneq (by
        calc
          recohSupportProbe chi (paramSupport ((a, d), v)) =
              recohSupportProbe chi U :=
            (recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hU).symm
          _ = recohSupportProbe chi T := heq3.symm
          _ = recohSupportProbe chi (paramSupport ((a, d), -v)) :=
            recoh_probe_constant_on_torsion_orbit chi htrivial _ _ hT)).elim
    · exact hQ hT hU heq2





end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r : Nat),
  @Eq.{1} Nat
      (Nat.card.{p2m_u_0}
        (@Subtype.{p2m_u_0 + 1} G fun x =>
          @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            x))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r) →
    ∀ (a d v : G),
      @Eq.{p2m_u_0 + 1} G
          (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
            (@instHAdd.{p2m_u_0} G
              (@AddCommMagma.toAdd.{p2m_u_0} G
                (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                  (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
            d d)
          (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
            (@Zero.toOfNat0.{p2m_u_0} G
              (@NegZeroClass.toZero.{p2m_u_0} G
                (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                  (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                    (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                      (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
        @Ne.{p2m_u_0 + 1} G d
            (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
              (@Zero.toOfNat0.{p2m_u_0} G
                (@NegZeroClass.toZero.{p2m_u_0} G
                  (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                    (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                      (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                        (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
          @Eq.{p2m_u_0 + 1} G
              (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                (@instHAdd.{p2m_u_0} G
                  (@AddCommMagma.toAdd.{p2m_u_0} G
                    (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                      (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                        (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                (@HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
                  (@instHAdd.{p2m_u_0} G
                    (@AddCommMagma.toAdd.{p2m_u_0} G
                      (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                        (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G
                          (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
                  v v)
                v)
              (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                (@Zero.toOfNat0.{p2m_u_0} G
                  (@NegZeroClass.toZero.{p2m_u_0} G
                    (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                      (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                        (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                          (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
            @Ne.{p2m_u_0 + 1} G v
                (@OfNat.ofNat.{p2m_u_0} G (nat_lit 0)
                  (@Zero.toOfNat0.{p2m_u_0} G
                    (@NegZeroClass.toZero.{p2m_u_0} G
                      (@SubNegZeroMonoid.toNegZeroClass.{p2m_u_0} G
                        (@SubtractionMonoid.toSubNegZeroMonoid.{p2m_u_0} G
                          (@SubtractionCommMonoid.toSubtractionMonoid.{p2m_u_0} G
                            (@AddCommGroup.toDivisionAddCommMonoid.{p2m_u_0} G inst))))))) →
              @Exists.{p2m_u_0 + 1}
                (Fin
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                  @AddChar.{p2m_u_0, 0} G
                    (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                      (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                    Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                fun bank =>
                @Set.InjOn.{p2m_u_0, 0} (Finset.{p2m_u_0} G)
                  (Fin
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    Complex)
                  (fun T i => @Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)
                  (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                    (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G))
                    (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2
                      (@Couret.STROBO2TORS.paramSupport.{p2m_u_0} G inst inst_1
                        (@Prod.mk.{p2m_u_0, p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} G G) G
                          (@Prod.mk.{p2m_u_0, p2m_u_0} G G a d) v)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_bank_on_param_fibre

