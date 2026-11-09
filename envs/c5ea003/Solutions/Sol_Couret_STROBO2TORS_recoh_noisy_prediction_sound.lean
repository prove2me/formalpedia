-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_noisy_prediction_sound
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:56:34.119911+00:00
-- url     : https://prove2.me/submissions/5b8df081-0dd6-4390-8732-b00220b309d5

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



/-- Approximate predictions consume part of the geometric error budget. -/
theorem p2m_local_recoh_noisy_prediction_sound (truth prediction observed : ℂ)
    (η τ : ℝ) (hpred : ‖prediction - truth‖ ≤ η)
    (hfit : ‖observed - prediction‖ ≤ τ) :
    ‖observed - truth‖ ≤ τ + η := by
  calc
    ‖observed - truth‖ = ‖(observed - prediction) + (prediction - truth)‖ := by
      congr 1
      ring
    _ ≤ ‖observed - prediction‖ + ‖prediction - truth‖ := norm_add_le _ _
    _ ≤ τ + η := add_le_add hfit hpred





















end Couret.STROBO2TORS


theorem solution : ∀ (truth prediction observed : Complex) (η τ : Real),
  @LE.le.{0} Real Real.instLE
      (@Norm.norm.{0} Complex Complex.instNorm
        (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) prediction truth))
      η →
    @LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} Complex Complex.instNorm
          (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) observed prediction))
        τ →
      @LE.le.{0} Real Real.instLE
        (@Norm.norm.{0} Complex Complex.instNorm
          (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub) observed truth))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) τ η) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_noisy_prediction_sound

