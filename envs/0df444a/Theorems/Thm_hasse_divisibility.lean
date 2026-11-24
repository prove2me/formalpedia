-- Prove2me | Theorems.Thm_hasse_divisibility
-- name    : hasse_divisibility
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:27.312804+00:00
-- url     : https://prove2.me/theorems/71c795bb-c69d-4c18-b4bf-d9bb21ff55fb
-- title:
--   Hasse derivative vanishing forces root multiplicity
-- statement:
--   Let f be a polynomial over a field and a a field element. If every Hasse derivative of order k < ℓ vanishes at a, then (X − a)^ℓ divides f.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/HasseDerivatives.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/HasseDerivatives.lean lines 591–628; SHA256 52716d7f8f075321c272319ddf388e0d1218878519fbf0e51588773d3636d49b.

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

theorem hasse_divisibility (F : Type*) [Field F] (f : Polynomial F) (a : F) (ℓ : ℕ)
    (hvan : ∀ k < ℓ, (hasseDerivOp F k f).eval a = 0) :
    (Polynomial.X - Polynomial.C a)^ℓ ∣ f := by sorry
