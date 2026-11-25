-- Prove2me | Theorems.Thm_riemann_hypothesis_hec
-- name    : riemann_hypothesis_hec
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:17.734482+00:00
-- url     : https://prove2.me/theorems/a554bcec-01af-4ced-baa3-c226d79af38b
-- title:
--   Uniform weak square-root estimate for affine quadratic curves
-- statement:
--   Let F be a finite field of size q and let f have degree m ≥ 3. Assume f is not a square over the algebraic closure and q > 6m. If N counts the affine solutions of y² = f(x), then |q − N| < 5m√q.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 577–643; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

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

theorem riemann_hypothesis_hec
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hm3 : 3 ≤ f.natDegree)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
        g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hq6m : q > 6 * f.natDegree) :
    |((q : ℝ) - (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ))|
      < (5 : ℝ) * (f.natDegree : ℝ) * Real.sqrt (q : ℝ) := by sorry
