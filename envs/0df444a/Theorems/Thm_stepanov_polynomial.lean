-- Prove2me | Theorems.Thm_stepanov_polynomial
-- name    : stepanov_polynomial
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:35:45.133312+00:00
-- url     : https://prove2.me/theorems/c47d6ae5-4b12-470d-8bc2-da0be3c986b6
-- title:
--   Existence of a nonzero Stepanov polynomial with prescribed multiplicity
-- statement:
--   Let F be an odd finite field of size q, and let f have degree m ≥ 3 and be nonsquare over the algebraic closure. If q > 6m and 0 < ℓ ≤ q/3, then for every a ∈ F there is a nonzero polynomial R with natDegree(R) < mq + ℓq/2 + ℓ²m such that DₖR(x) = 0 whenever k < ℓ and either f(x) = 0 or f(x)^((q−1)/2) = a.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovPolynomial.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovPolynomial.lean lines 7–282; SHA256 80a9a4f0c3e2e3d6b4e402005021de097233638fd19ed2f769c11fbdcdf65968.

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
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

theorem stepanov_polynomial
  (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
  (f : Polynomial F) (q ℓ : ℕ) (a : F)
  (hq : q = Fintype.card F) (hm3 : 3 ≤ f.natDegree)
  (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
  (hq6m : q > 6 * f.natDegree) (hℓ_pos : 0 < ℓ) (hl : ℓ ≤ q / 3) :
  ∃ r : Polynomial F,
    r ≠ 0 ∧
    ((r.natDegree : ℝ) <
      ((f.natDegree * q : ℕ) : ℝ) +
        ((ℓ * q : ℕ) : ℝ) / 2 +
        ((ℓ * ℓ * f.natDegree : ℕ) : ℝ)) ∧
    (∀ x ∈ S_a F f ((q - 1) / 2) a, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) := by sorry
