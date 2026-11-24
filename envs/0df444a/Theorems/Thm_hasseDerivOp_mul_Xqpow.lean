-- Prove2me | Theorems.Thm_hasseDerivOp_mul_Xqpow
-- name    : hasseDerivOp_mul_Xqpow
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:27.495966+00:00
-- url     : https://prove2.me/theorems/9b931c34-49e4-4721-ac3f-103590879b7a
-- title:
--   Low Hasse derivatives ignore Frobenius monomial factors
-- statement:
--   For a finite field of size q, every k < q, polynomial P, and natural j satisfy Dₖ(P·Xʲᑫ) = (DₖP)·Xʲᑫ, where Dₖ is the kth Hasse derivative.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovAuxiliary.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovAuxiliary.lean lines 155–284; SHA256 5c716bf363ff271afb18158456c5f40ab18777e3eafdb03903953fdbc5d982a8.

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

theorem hasseDerivOp_mul_Xqpow
  (F : Type*) [Field F] [Fintype F]
  (q k : ℕ) (hq : q = Fintype.card F) (hkq : k < q)
  (P : Polynomial F) (j : ℕ) :
  hasseDerivOp F k (P * (Polynomial.X : Polynomial F)^(j * q)) =
    hasseDerivOp F k P * (Polynomial.X : Polynomial F)^(j * q) := by sorry
