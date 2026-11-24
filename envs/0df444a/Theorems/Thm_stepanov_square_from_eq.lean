-- Prove2me | Theorems.Thm_stepanov_square_from_eq
-- name    : stepanov_square_from_eq
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:20.823672+00:00
-- url     : https://prove2.me/theorems/77705afd-5b0c-4939-80f3-141a363fa884
-- title:
--   A square-ratio polynomial identity implies geometric squareness
-- statement:
--   Over any field F, suppose f₀ ≠ 0, s ≠ 0, and polynomials r,s,f satisfy r²f = f₀s². Then f becomes the square of a polynomial over the algebraic closure of F.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovNonSquare.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovNonSquare.lean lines 4–92; SHA256 c068582a3c56d317a522c43afeafce6091ae371a22640b79e14df39de7a6fa88.

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

theorem stepanov_square_from_eq (F : Type*) [Field F]
    (f : Polynomial F) (r s : Polynomial F) (f₀ : F)
    (hf₀_ne_zero : f₀ ≠ 0) (hs_ne_zero : s ≠ 0)
    (heq : r * r * f = s * s * Polynomial.C f₀) :
    ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f := by sorry
