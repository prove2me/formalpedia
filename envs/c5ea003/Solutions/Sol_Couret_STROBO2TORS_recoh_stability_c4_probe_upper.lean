-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stability_c4_probe_upper
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:11.494288+00:00
-- url     : https://prove2.me/submissions/208b06a4-9b50-4f6c-b218-7e06cbe784d1

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_finite_character_norm_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
Quantitative separation of character readings.  A separation statement uses
an existential coordinate; no finite maximum, nonempty bank, or nontrivial
fibre is silently assumed.  In particular singleton fibres and empty banks
are handled by the same definition.
-/

namespace Couret.STROBO2TORS



variable {G : Type*} [AddCommGroup G] [DecidableEq G]













variable [Fintype G]











/-- No character, hence no unweighted bank in the coordinatewise metric,
separates the C4 obstruction by more than two. -/
theorem p2m_local_recoh_stability_c4_probe_upper (chi : AddChar (ZMod 4) ℂ) :
    ‖recohSupportProbe chi recohStabilityC4Left -
      recohSupportProbe chi recohStabilityC4Right‖ ≤ 2 := by
  have hleft : recohSupportProbe chi recohStabilityC4Left =
      chi 0 + chi 1 + chi 2 := by
    exact recoh_support_probe_three chi 0 1 2 (by decide) (by decide) (by decide)
  have hright : recohSupportProbe chi recohStabilityC4Right =
      chi 0 + chi 2 + chi 3 := by
    exact recoh_support_probe_three chi 0 2 3 (by decide) (by decide) (by decide)
  rw [hleft, hright]
  have h : chi 0 + chi 1 + chi 2 - (chi 0 + chi 2 + chi 3) =
      chi 1 - chi 3 := by ring
  rw [h]
  calc
    ‖chi 1 - chi 3‖ ≤ ‖chi 1‖ + ‖chi 3‖ := norm_sub_le _ _
    _ = 2 := by rw [recoh_finite_character_norm_one, recoh_finite_character_norm_one]; norm_num



end Couret.STROBO2TORS


theorem solution : ∀
  (chi :
    @AddChar.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  @LE.le.{0} Real Real.instLE
    (@Norm.norm.{0} Complex Complex.instNorm
      (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
        (@Couret.STROBO2TORS.recohSupportProbe.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          chi Couret.STROBO2TORS.recohStabilityC4Left)
        (@Couret.STROBO2TORS.recohSupportProbe.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          chi Couret.STROBO2TORS.recohStabilityC4Right)))
    (@OfNat.ofNat.{0} Real (nat_lit 2)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stability_c4_probe_upper

