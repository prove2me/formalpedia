-- Prove2me | Theorems.Thm_stepanov_system_constraint_count
-- name    : stepanov_system_constraint_count
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:35:34.37657+00:00
-- url     : https://prove2.me/theorems/d6c37c69-b192-4b95-80a4-cbe1a9c19df2
-- title:
--   Closed bounds for the Stepanov constraint count
-- statement:
--   For natural parameters, assume m ≥ 2, q > 6m, 0 < ℓ ≤ q/3, J ≥ 1, and d = ⌈(q−m)/2⌉−1. If B ≤ Σₖ<ℓ(J+d+k(m−1)), then B ≤ ℓJ+ℓd+ℓ(ℓ−1)(m−1)/2 and, over the reals, B < ℓ[J+(q−m)/2+(ℓ−1)(m−1)/2].
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovSystem.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovSystem.lean lines 33–206; SHA256 8598e8f2f5a5feb4a726f52cf8cda87aea55e087771de3eb377b792d7c6081ff.

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

theorem stepanov_system_constraint_count
    (ℓ J d m q : ℕ) (B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : 6 * m < q)
    (_hℓ : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (_hJ : 1 ≤ J)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1))) :
    B ≤ ℓ * J + ℓ * d + ℓ * (ℓ - 1) * (m - 1) / 2 ∧
    (B : ℝ) <
      (ℓ : ℝ) * ((J : ℝ) + ((q : ℝ) - (m : ℝ)) / 2 +
        (((ℓ : ℝ) - 1) * ((m : ℝ) - 1)) / 2) := by sorry
