-- Prove2me | Theorems.Thm_coefficient_transformation_shift
-- name    : coefficient_transformation_shift
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:20.652807+00:00
-- url     : https://prove2.me/theorems/9b0c0241-61d5-4290-9bb1-e509c2f8beec
-- title:
--   Binomial transformation of polynomial coefficient blocks
-- statement:
--   For a field element a, natural q and J, and polynomials Aⱼ, the sum Σⱼ<J Aⱼ(X^q+a)ʲ equals Σₖ<J BₖXᵏᑫ, where Bₖ = Σₖ≤j<J binom(j,k)a^(j−k)Aⱼ and the field-valued factors act as polynomial scalars.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovNonSquare.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovNonSquare.lean lines 109–236; SHA256 c068582a3c56d317a522c43afeafce6091ae371a22640b79e14df39de7a6fa88.

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

theorem coefficient_transformation_shift (F : Type*) [Field F]
    (a : F) (q J : ℕ) (A : ℕ → Polynomial F) :
    ∑ j ∈ Finset.range J, A j * (Polynomial.X ^ q + Polynomial.C a) ^ j =
      ∑ k ∈ Finset.range J,
        (∑ j ∈ Finset.Ico k J,
            (Nat.choose j k : F) • (Polynomial.C a) ^ (j - k) * A j) *
          Polynomial.X ^ (k * q) := by sorry
