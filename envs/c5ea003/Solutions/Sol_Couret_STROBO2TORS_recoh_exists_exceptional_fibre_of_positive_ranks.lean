-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_exists_exceptional_fibre_of_positive_ranks
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:32.830966+00:00
-- url     : https://prove2.me/submissions/cadcaf31-6dda-4531-9908-51763d9429b5

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
import Theorems.Thm_Couret_STROBO2TORS_mem_exceptionalSupports_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_mem_exceptionalSupports
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















/-- Positive two- and three-torsion ranks produce an actual exceptional
triple fibre, so the `r+1` worst-case budget is attained. -/
theorem p2m_local_recoh_exists_exceptional_fibre_of_positive_ranks
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (hcard2 : Nat.card (recohTorsionSubgroup (G := G) 2) = 2 ^ r)
    (hcard3 : Nat.card (recohTorsionSubgroup (G := G) 3) = 3 ^ s) :
    ∃ S : Finset G, S.card = 3 ∧
      (squareFibre S).card = 2 * (twoTorsion : Finset G).card := by
  classical
  have h2 : 1 < Nat.card (recohTorsionSubgroup (G := G) 2) := by
    rw [hcard2]
    exact one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (Nat.ne_of_gt hr)
  have h3 : 1 < Nat.card (recohTorsionSubgroup (G := G) 3) := by
    rw [hcard3]
    exact one_lt_pow₀ (by decide : 1 < (3 : ℕ)) (Nat.ne_of_gt hs)
  letI : Nontrivial (recohTorsionSubgroup (G := G) 2) :=
    Finite.one_lt_card_iff_nontrivial.mp h2
  letI : Nontrivial (recohTorsionSubgroup (G := G) 3) :=
    Finite.one_lt_card_iff_nontrivial.mp h3
  obtain ⟨d, hd0⟩ := exists_ne (0 : recohTorsionSubgroup (G := G) 2)
  obtain ⟨v, hv0⟩ := exists_ne (0 : recohTorsionSubgroup (G := G) 3)
  have hd : (d : G) + (d : G) = 0 := by
    simpa only [recoh_mem_torsion_subgroup, two_nsmul] using d.property
  have hv : ((v : G) + (v : G)) + (v : G) = 0 := by
    simpa only [recoh_mem_torsion_subgroup, succ_nsmul, zero_nsmul, zero_add]
      using v.property
  have hd0' : (d : G) ≠ 0 := fun h => hd0 (Subtype.ext h)
  have hv0' : (v : G) ≠ 0 := fun h => hv0 (Subtype.ext h)
  refine ⟨paramSupport (((0 : G), (d : G)), (v : G)), ?_⟩
  exact (mem_exceptionalSupports_card _).mp
    (paramSupport_mem_exceptionalSupports 0 (d : G) (v : G) hd hd0' hv hv0')

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (r s : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) r →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s →
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
          @Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun S =>
            And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Eq.{1} Nat
                (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
                  (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Finset.card.{p2m_u_0} G (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2)))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_exists_exceptional_fibre_of_positive_ranks

