-- Prove2me | Theorems.Thm_auxiliary_derivatives
-- name    : auxiliary_derivatives
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:26.705819+00:00
-- url     : https://prove2.me/theorems/411becb6-fc88-4972-b149-188d23a2c751
-- title:
--   Degree-controlled quotient polynomials for Hasse derivatives
-- statement:
--   Let f be a polynomial of natural degree m over a field, and let r and s have natural degree at most d. For k ≤ ℓ there exist rₖ and sₖ satisfying Dₖ(f^ℓr) = rₖf^(ℓ−k) and Dₖ(f^(ℓ+c)s) = sₖf^(ℓ+c−k), with both quotient degrees at most d + k(m−1), using natural subtraction.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovAuxiliary.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovAuxiliary.lean lines 4–153; SHA256 5c716bf363ff271afb18158456c5f40ab18777e3eafdb03903953fdbc5d982a8.

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

theorem auxiliary_derivatives (F : Type*) [Field F]
    (f : Polynomial F) (m d ℓ c : ℕ)
    (hfdeg : f.natDegree = m)
    (rj sj : Polynomial F) (hr : rj.natDegree ≤ d) (hs : sj.natDegree ≤ d)
    (k : ℕ) (hk : k ≤ ℓ) :
  ∃ rjk sjk : Polynomial F,
    hasseDerivOp F k (f^ℓ * rj) = rjk * f^(ℓ - k) ∧
    hasseDerivOp F k (f^(ℓ + c) * sj) = sjk * f^(ℓ + c - k) ∧
    rjk.natDegree ≤ d + k * (m - 1) ∧ sjk.natDegree ≤ d + k * (m - 1) := by sorry
