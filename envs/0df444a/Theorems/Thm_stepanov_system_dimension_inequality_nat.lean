-- Prove2me | Theorems.Thm_stepanov_system_dimension_inequality_nat
-- name    : stepanov_system_dimension_inequality_nat
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:35:34.613852+00:00
-- url     : https://prove2.me/theorems/11711f87-c577-4258-8afc-afc82e7563c7
-- title:
--   The Stepanov coefficient space has more dimensions than constraints
-- statement:
--   Let q, m, ℓ be natural numbers with m ≥ 2, q > 6m, and 0 < ℓ ≤ q/3. Set D = ⌈(q−m)/2⌉ and J = ⌈ℓ/2+ℓ²m/q⌉. If the natural number B is at most Σₖ<ℓ(J+D−1+k(m−1)), then B < 2JD.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovSystem.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovSystem.lean lines 263–569; SHA256 8598e8f2f5a5feb4a726f52cf8cda87aea55e087771de3eb377b792d7c6081ff.

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

theorem stepanov_system_dimension_inequality_nat
    (q m ℓ : ℕ)
    (hm_ge_two : 2 ≤ m) (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hℓ_pos : 0 < ℓ)
    (B : ℕ)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) +
        (Nat.ceil (((q : ℚ) - m) / 2) - 1) + k * (m - 1))) :
    let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
    2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B := by sorry
