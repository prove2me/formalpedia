-- Prove2me | Theorems.Thm_stepanov_nonzero_polynomial_equality
-- name    : stepanov_nonzero_polynomial_equality
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T14:18:20.870464+00:00
-- url     : https://prove2.me/theorems/a751cc52-ae83-4372-8dc6-96cedd9fa3dd
-- title:
--   A low-degree Stepanov congruence forces a polynomial identity
-- statement:
--   Over an odd finite field of size q, put c = (q−1)/2 and m = natDegree(f). If 2·natDegree(r)+m < q, 2·natDegree(s)+m < q, and X^q divides r + sfᶜ, then r²f = s²·f(0) as polynomials.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovNonSquare.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovNonSquare.lean lines 331–443; SHA256 c068582a3c56d317a522c43afeafce6091ae371a22640b79e14df39de7a6fa88.

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

theorem stepanov_nonzero_polynomial_equality
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f r s : Polynomial F) (q m c : ℕ)
  (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hc : c = (q - 1) / 2)
  (hrdeg : 2 * r.natDegree + m < q) (hsdeg : 2 * s.natDegree + m < q)
  (hcong : Polynomial.X ^ q ∣ (r + s * f ^ c)) :
  r * r * f = s * s * Polynomial.C (f.eval 0) := by sorry
