-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_noisy_recovered_candidates_square_sound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:33.920108+00:00
-- url     : https://prove2.me/submissions/5f1ec80c-f1bf-44fe-8655-34192ab054fc

import Aesop
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS







variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2











/-- Recovered candidates stay in the exact square fibre regardless of
the observations, because recovery always translates by two-torsion. -/
theorem p2m_local_recoh_noisy_recovered_candidates_square_sound [Fintype G]
    (S : Finset G) (representatives : Finset (Finset G))
    (hrepresentatives : representatives ⊆ squareFibre S)
    (e : H₂ ≃+ (J → ZMod 2))
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) :
    recohNoisyRecoveredCandidates representatives e predicted observed radius ⊆ squareFibre S := by
  intro T hT
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hT
  obtain ⟨hBcard, hBsq⟩ := (mem_squareFibre S B).mp (hrepresentatives hB)
  let u := recohIndexedRecoverTranslation e
    (fun i => recohRationalSignSame (predicted B i) (observed i) radius)
  have hu : (u : G) + (u : G) = 0 := by
    simpa only [recoh_mem_torsion_subgroup, two_nsmul] using u.property
  change translateSupport B (u : G) ∈ squareFibre S
  apply (mem_squareFibre S _).mpr
  refine ⟨by rw [translateSupport_card]; exact hBcard, ?_⟩
  intro z
  exact (hBsq z).trans (orderedSquare_translate_of_card_three B hBcard (u : G) z hu).symm









end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} {J : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G) (representatives : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instHasSubset.{p2m_u_0} (Finset.{p2m_u_0} G)) representatives
      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) →
    ∀
      (e :
        @AddEquiv.{p2m_u_0, p2m_u_1}
          (@Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              x)
          (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Pi.instAdd.{p2m_u_1, 0} J (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            fun i =>
            @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Semifield.toDivisionSemiring.{0}
                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        Nat.fact_prime_two)))))))
      (predicted : Finset.{p2m_u_0} G → J → Couret.STROBO2TORS.RecohRationalComplex)
      (observed : J → Couret.STROBO2TORS.RecohRationalComplex) (radius : Rat),
      @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Finset.instHasSubset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.recohNoisyRecoveredCandidates.{p2m_u_0, p2m_u_1} G J inst inst_1 representatives e
          predicted observed radius)
        (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_noisy_recovered_candidates_square_sound

