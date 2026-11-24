-- Prove2me | Theorems.Thm_stepanovHasseQuotMap_mul
-- name    : stepanovHasseQuotMap_mul
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:35:46.947581+00:00
-- url     : https://prove2.me/theorems/adb70e80-83cc-4381-931b-81b10dc2370e
-- title:
--   The linear Hasse quotient map reconstructs its numerator
-- statement:
--   For a nonzero polynomial f over a field, all natural r and k, and every polynomial p, stepanovHasseQuotMap(f,r,k)(p) multiplied by f^(r−k) equals Dₖ(pfʳ).
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovSystem.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovSystem.lean lines 677–705; SHA256 8598e8f2f5a5feb4a726f52cf8cda87aea55e087771de3eb377b792d7c6081ff.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovSystem
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem stepanovHasseQuotMap_mul
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p * f ^ (r - k) =
      hasseDerivOp F k (p * f ^ r) := by sorry
