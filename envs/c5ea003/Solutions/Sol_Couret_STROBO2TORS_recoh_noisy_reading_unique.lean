-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_noisy_reading_unique
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:38.33278+00:00
-- url     : https://prove2.me/submissions/c467b40b-ca12-492d-8f0e-e0bf8fe2d038

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

/-- Two candidates inside coordinatewise error balls whose radii sum to
less than the bank separation must coincide. -/
theorem p2m_local_recoh_noisy_reading_unique {X I : Type*}
    (reading : X → I → ℂ) (candidates : Finset X) (δ : ℝ)
    (hsep : RecohReadingSeparated reading candidates δ)
    (observed : I → ℂ) (S T : X) (hS : S ∈ candidates) (hT : T ∈ candidates)
    (εS εT : ℝ) (hbudget : εS + εT < δ)
    (hSerr : ∀ i, ‖observed i - reading S i‖ ≤ εS)
    (hTerr : ∀ i, ‖observed i - reading T i‖ ≤ εT) : S = T := by
  by_contra hST
  obtain ⟨i, hi⟩ := hsep S hS T hT hST
  have hbound : ‖reading S i - reading T i‖ ≤ εS + εT := by
    calc
      ‖reading S i - reading T i‖ =
          ‖(reading S i - observed i) + (observed i - reading T i)‖ := by
        congr 1
        ring
      _ ≤ ‖reading S i - observed i‖ + ‖observed i - reading T i‖ := norm_add_le _ _
      _ ≤ εS + εT := add_le_add (by simpa only [norm_sub_rev] using hSerr i) (hTerr i)
  exact (not_lt_of_ge (hi.trans hbound)) hbudget























end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {X : Type p2m_u_0} {I : Type p2m_u_1} (reading : X → I → Complex) (candidates : Finset.{p2m_u_0} X) (δ : Real),
  @Couret.STROBO2TORS.RecohReadingSeparated.{p2m_u_0, p2m_u_1} X I reading candidates δ →
    ∀ (observed : I → Complex) (S T : X),
      @Membership.mem.{p2m_u_0, p2m_u_0} X (Finset.{p2m_u_0} X)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} X) X (@Finset.instSetLike.{p2m_u_0} X))
          candidates S →
        @Membership.mem.{p2m_u_0, p2m_u_0} X (Finset.{p2m_u_0} X)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} X) X (@Finset.instSetLike.{p2m_u_0} X))
            candidates T →
          ∀ (εS εT : Real),
            @LT.lt.{0} Real Real.instLT (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) εS εT)
                δ →
              (∀ (i : I),
                  @LE.le.{0} Real Real.instLE
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) (observed i)
                        (reading S i)))
                    εS) →
                (∀ (i : I),
                    @LE.le.{0} Real Real.instLE
                      (@Norm.norm.{0} Complex Complex.instNorm
                        (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                          (observed i) (reading T i)))
                      εT) →
                  @Eq.{p2m_u_0 + 1} X S T := @_root_.Couret.STROBO2TORS.p2m_local_recoh_noisy_reading_unique

