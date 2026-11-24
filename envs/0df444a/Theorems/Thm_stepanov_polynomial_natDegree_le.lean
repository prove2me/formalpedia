-- Prove2me | Theorems.Thm_stepanov_polynomial_natDegree_le
-- name    : stepanov_polynomial_natDegree_le
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:21.233056+00:00
-- url     : https://prove2.me/theorems/efc604c5-23a8-4585-a35f-c35428fc47f3
-- title:
--   Explicit degree bound for the Stepanov polynomial ansatz
-- statement:
--   Over a finite field, if f has natural degree m and each rⱼ and sⱼ for j < J has natural degree at most d, then R = f^ℓΣⱼ<J(rⱼ + sⱼfᶜ)Xʲᑫ has natural degree at most ℓm + d + cm + (J−1)q.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovDegreeBounds.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovDegreeBounds.lean lines 4–57; SHA256 38850d46521d613a9f50eae56f56567508698f436a2c7b09899c555cb0dc3474.

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

theorem stepanov_polynomial_natDegree_le (F : Type*) [Field F] [Fintype F] (f : Polynomial F)
  (q m ℓ c d J : ℕ) (hfdeg : f.natDegree = m) (rj sj : ℕ → Polynomial F)
  (hdegr : ∀ j < J, (rj j).natDegree ≤ d) (hdegs : ∀ j < J, (sj j).natDegree ≤ d) :
  (f^ℓ * (Finset.sum (Finset.range J)
    (fun j => ((rj j) + (sj j) * f^c) * Polynomial.X^(j*q)))).natDegree
      ≤ ℓ * m + d + c * m + (J - 1) * q := by sorry
