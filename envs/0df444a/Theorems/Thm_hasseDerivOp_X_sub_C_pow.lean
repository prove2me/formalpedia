-- Prove2me | Theorems.Thm_hasseDerivOp_X_sub_C_pow
-- name    : hasseDerivOp_X_sub_C_pow
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:19:22.005425+00:00
-- url     : https://prove2.me/theorems/8d927277-b446-4747-90e2-5b7181847543
-- title:
--   Hasse derivative of a shifted monomial
-- statement:
--   For any field, any a, and natural numbers k ≤ r, the kth Hasse derivative of (X − a)ʳ is binom(r,k)(X − a)ʳ⁻ᵏ.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/HasseDerivatives.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/HasseDerivatives.lean lines 210–306; SHA256 52716d7f8f075321c272319ddf388e0d1218878519fbf0e51588773d3636d49b.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
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

theorem hasseDerivOp_X_sub_C_pow (F : Type*) [Field F]
    (k r : ℕ) (hk : k ≤ r) :
    ∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k) := by sorry
