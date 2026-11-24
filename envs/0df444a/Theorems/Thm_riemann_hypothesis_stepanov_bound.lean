-- Prove2me | Theorems.Thm_riemann_hypothesis_stepanov_bound
-- name    : riemann_hypothesis_stepanov_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:23.5874+00:00
-- url     : https://prove2.me/theorems/0d9a1826-2416-41fb-9aa3-58c3e4110331
-- title:
--   Stepanov bound for a prescribed quadratic-character level
-- statement:
--   Let F be a finite field of odd characteristic and size q, and let f have degree m ≥ 3, be nonsquare over the algebraic closure, and satisfy q > 6m. For every a ∈ F, the set Sₐ = {x : f(x) = 0 or f(x)^((q−1)/2) = a} has cardinality strictly less than q/2 + 2m⌈√q⌉.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 94–234; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovPolynomial
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

theorem riemann_hypothesis_stepanov_bound
  (F : Type*) [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q : ℕ) (a : F)
  (hq : q = Fintype.card F)
  (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree)
  [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) a)] :
  (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) a} : ℝ)
    < (q : ℝ) / 2 + 2 * (f.natDegree : ℝ) * (Nat.ceil (Real.sqrt q) : ℝ) := by sorry
