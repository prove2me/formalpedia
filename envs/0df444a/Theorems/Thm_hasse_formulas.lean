-- Prove2me | Theorems.Thm_hasse_formulas
-- name    : hasse_formulas
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:19:29.9008+00:00
-- url     : https://prove2.me/theorems/5ec02077-29a2-4a43-b804-a25559679913
-- title:
--   Hasse derivative formulas and quotient degree bound
-- statement:
--   Over any field, for natural numbers k ≤ r, the kth Hasse derivative of (X − a)ʳ equals binom(r,k)(X − a)ʳ⁻ᵏ. For arbitrary polynomials f and g, gʳ⁻ᵏ divides the kth Hasse derivative of f·gʳ, and the degree of the quotient is at most deg(f) + k·deg(g) − k, with the formal bottom-degree and truncated natural-subtraction conventions.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/HasseDerivatives.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/HasseDerivatives.lean lines 421–589; SHA256 52716d7f8f075321c272319ddf388e0d1218878519fbf0e51588773d3636d49b.

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

theorem hasse_formulas (F : Type*) [Field F] (k r : ℕ) (hk : k ≤ r) :
  (∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k))
  ∧
  (∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) ∧
      Polynomial.degree ((hasseDerivOp F k (f * g^r)) / (g^(r - k))) ≤
        (match (Polynomial.degree f + (k : WithBot ℕ) * Polynomial.degree g) with
         | ⊥ => ⊥
         | some n => ((n - k : ℕ) : WithBot ℕ))) := by sorry
