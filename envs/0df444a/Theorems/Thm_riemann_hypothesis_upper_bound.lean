-- Prove2me | Theorems.Thm_riemann_hypothesis_upper_bound
-- name    : riemann_hypothesis_upper_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:17.626533+00:00
-- url     : https://prove2.me/theorems/fcd722f1-7570-43df-a765-853aad8b20ae
-- title:
--   Stepanov upper bound for an affine quadratic curve
-- statement:
--   Let F be a finite field of odd characteristic with q elements. Let f have degree m ≥ 3, remain nonsquare over the algebraic closure, and satisfy q > 6m. Then the number N of affine solutions of y² = f(x) satisfies N < q + 4m⌈√q⌉.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 236–362; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

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

theorem riemann_hypothesis_upper_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      < (q : ℝ) + 4 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by sorry
