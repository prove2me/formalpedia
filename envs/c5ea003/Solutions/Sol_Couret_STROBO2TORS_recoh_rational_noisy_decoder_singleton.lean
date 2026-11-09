-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_rational_noisy_decoder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:17:56.616286+00:00
-- url     : https://prove2.me/submissions/778c0439-9ece-4d7d-b0be-0817d43952fa

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_prediction_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_ball_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_card_le_one
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











theorem recoh_mem_rational_noisy_decoder_iff {X I : Type*}
    [DecidableEq X] [Fintype I]
    (candidates : Finset X) (predicted : X → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (S : X) :
    S ∈ recohRationalNoisyDecoder candidates predicted observed radius ↔
      S ∈ candidates ∧ 0 ≤ radius ∧
        ∀ i, ‖recohRationalComplexValue (observed i) -
          recohRationalComplexValue (predicted S i)‖ ≤ (radius : ℝ) := by
  rw [recohRationalNoisyDecoder, Finset.mem_filter]
  constructor
  · rintro ⟨hS, hr, h⟩
    exact ⟨hS, hr, fun i => (recoh_rational_ball_iff _ _ radius hr).mp (h i)⟩
  · rintro ⟨hS, hr, h⟩
    exact ⟨hS, hr, fun i => (recoh_rational_ball_iff _ _ radius hr).mpr (h i)⟩





/-- Completeness requires both an included true candidate and enough
acceptance radius for measurement error plus prediction error. -/
theorem recoh_rational_noisy_decoder_complete {X I : Type*}
    [DecidableEq X] [Fintype I]
    (reading : X → I → ℂ) (candidates : Finset X)
    (predicted : X → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (ε η : ℝ)
    (hradius : 0 ≤ radius) (S : X) (hS : S ∈ candidates)
    (hpred : ∀ i, ‖recohRationalComplexValue (predicted S i) - reading S i‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) - reading S i‖ ≤ ε)
    (hbudget : ε + η ≤ (radius : ℝ)) :
    S ∈ recohRationalNoisyDecoder candidates predicted observed radius := by
  apply (recoh_mem_rational_noisy_decoder_iff candidates predicted observed radius S).mpr
  refine ⟨hS, hradius, ?_⟩
  intro i
  apply le_trans ?_ hbudget
  exact recoh_noisy_prediction_sound _ _ _ η ε
    (by simpa only [norm_sub_rev] using hpred i) (hobs i)

/-- With a true included candidate, soundness and the strict separation
budget strengthen the output contract from at-most-one to exactly-one. -/
theorem p2m_local_recoh_rational_noisy_decoder_singleton {X I : Type*}
    [DecidableEq X] [Fintype I]
    (reading : X → I → ℂ) (candidates : Finset X)
    (predicted : X → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (ε η δ : ℝ)
    (hradius : 0 ≤ radius) (S : X) (hS : S ∈ candidates)
    (hsep : RecohReadingSeparated reading candidates δ)
    (hpred : ∀ T ∈ candidates, ∀ i,
      ‖recohRationalComplexValue (predicted T i) - reading T i‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) - reading S i‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : 2 * ((radius : ℝ) + η) < δ) :
    recohRationalNoisyDecoder candidates predicted observed radius = {S} := by
  have hmem := recoh_rational_noisy_decoder_complete reading candidates predicted observed
    radius ε η hradius S hS (hpred S hS) hobs hcomplete
  have hcard := recoh_rational_noisy_decoder_card_le_one reading candidates predicted observed
    radius η δ hsep hpred hunique
  ext T
  constructor
  · intro hT
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hcard T hT S hmem)
  · intro hT
    simpa only [Finset.mem_singleton.mp hT] using hmem





end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {X : Type p2m_u_0} {I : Type p2m_u_1} [inst : DecidableEq.{p2m_u_0 + 1} X] [inst_1 : Fintype.{p2m_u_1} I]
  (reading : X → I → Complex) (candidates : Finset.{p2m_u_0} X)
  (predicted : X → I → Couret.STROBO2TORS.RecohRationalComplex) (observed : I → Couret.STROBO2TORS.RecohRationalComplex)
  (radius : Rat) (ε η δ : Real),
  @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) radius →
    ∀ (S : X),
      @Membership.mem.{p2m_u_0, p2m_u_0} X (Finset.{p2m_u_0} X)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} X) X (@Finset.instSetLike.{p2m_u_0} X))
          candidates S →
        @Couret.STROBO2TORS.RecohReadingSeparated.{p2m_u_0, p2m_u_1} X I reading candidates δ →
          (∀ (T : X),
              @Membership.mem.{p2m_u_0, p2m_u_0} X (Finset.{p2m_u_0} X)
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} X) X (@Finset.instSetLike.{p2m_u_0} X))
                  candidates T →
                ∀ (i : I),
                  @LE.le.{0} Real Real.instLE
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                        (Couret.STROBO2TORS.recohRationalComplexValue (predicted T i)) (reading T i)))
                    η) →
            (∀ (i : I),
                @LE.le.{0} Real Real.instLE
                  (@Norm.norm.{0} Complex Complex.instNorm
                    (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                      (Couret.STROBO2TORS.recohRationalComplexValue (observed i)) (reading S i)))
                  ε) →
              @LE.le.{0} Real Real.instLE (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ε η)
                  (@Rat.cast.{0} Real Real.instRatCast radius) →
                @LT.lt.{0} Real Real.instLT
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@Rat.cast.{0} Real Real.instRatCast radius) η))
                    δ →
                  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} X)
                    (@Couret.STROBO2TORS.recohRationalNoisyDecoder.{p2m_u_0, p2m_u_1} X I inst inst_1 candidates
                      predicted observed radius)
                    (@Singleton.singleton.{p2m_u_0, p2m_u_0} X (Finset.{p2m_u_0} X) (@Finset.instSingleton.{p2m_u_0} X)
                      S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_rational_noisy_decoder_singleton

