-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stability_c4_midpoint_ambiguous
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:09.070922+00:00
-- url     : https://prove2.me/submissions/9123a18d-eb3c-4836-b9dc-89664093d8e8

import Aesop
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_stability_c4_probe_upper
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohRationalComplex_e4146c64164f
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
Noise tolerance with explicit prediction error.  The executable decoder
below compares rational squared distances.  Its correctness theorem relates
those comparisons to the complex readings, accounting separately for the
measurement error, the prediction error, and the acceptance radius.

The candidate set is supplied explicitly.  Completeness requires the true
support to occur in that set; this module makes no ambient enumeration claim.
-/

namespace Couret.STROBO2TORS





















/-- The midpoint of readings separated by at most two lies in both
closed unit balls; the strict error threshold cannot be relaxed. -/
theorem recoh_midpoint_unit_balls (z w : ℂ) (h : ‖z - w‖ ≤ 2) :
    ‖(z + w) / 2 - z‖ ≤ 1 ∧ ‖(z + w) / 2 - w‖ ≤ 1 := by
  have hz : (z + w) / 2 - z = (w - z) / 2 := by ring
  have hw : (z + w) / 2 - w = (z - w) / 2 := by ring
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  constructor
  · rw [hz, norm_div, htwo, norm_sub_rev]
    linarith
  · rw [hw, norm_div, htwo]
    linarith

/-- The explicit C4 collision gives ambiguity at error at most one for
every bank, including banks with more than the minimum number of slots. -/
theorem p2m_local_recoh_stability_c4_midpoint_ambiguous
    {I : Type*} (bank : I → AddChar (ZMod 4) ℂ) :
    ∃ observed : I → ℂ, ∀ i,
      ‖observed i - recohSupportProbe (bank i) recohStabilityC4Left‖ ≤ 1 ∧
      ‖observed i - recohSupportProbe (bank i) recohStabilityC4Right‖ ≤ 1 := by
  refine ⟨fun i => (recohSupportProbe (bank i) recohStabilityC4Left +
    recohSupportProbe (bank i) recohStabilityC4Right) / 2, ?_⟩
  intro i
  exact recoh_midpoint_unit_balls _ _ (recoh_stability_c4_probe_upper (bank i))

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {I : Type p2m_u_0}
  (bank :
    I →
      @AddChar.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        (@AddMonoidWithOne.toAddMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (@AddGroupWithOne.toAddMonoidWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)),
  @Exists.{p2m_u_0 + 1} (I → Complex) fun observed =>
    ∀ (i : I),
      And
        (@LE.le.{0} Real Real.instLE
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) (observed i)
              (@Couret.STROBO2TORS.recohSupportProbe.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                (bank i) Couret.STROBO2TORS.recohStabilityC4Left)))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@LE.le.{0} Real Real.instLE
          (@Norm.norm.{0} Complex Complex.instNorm
            (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) (observed i)
              (@Couret.STROBO2TORS.recohSupportProbe.{0}
                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                (@Ring.toAddCommGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@CommRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                (bank i) Couret.STROBO2TORS.recohStabilityC4Right)))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stability_c4_midpoint_ambiguous

