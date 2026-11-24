-- Prove2me | Theorems.Thm_partition_N1_eq_q_sub_S_neg1
-- name    : partition_N1_eq_q_sub_S_neg1
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T14:18:26.064922+00:00
-- url     : https://prove2.me/theorems/78dacf46-7061-4a95-916b-8c8480729187
-- title:
--   Quadratic-residue inputs complement zeros and nonresidue inputs
-- statement:
--   Over a finite field of odd characteristic and size q, let c = (q−1)/2. The number of x satisfying f(x) ≠ 0 and f(x)ᶜ = 1 equals q minus the number satisfying f(x) = 0 or f(x)ᶜ = −1.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 484–558; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

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

theorem partition_N1_eq_q_sub_S_neg1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2)
    [DecidablePred (fun x : F => x ∈ S_a F f ((q - 1) / 2) (-1))] :
    (Fintype.card
        {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
          Polynomial.eval x f ≠ 0} : ℝ)
      = (q : ℝ) -
        (Fintype.card {x : F // x ∈ S_a F f ((q - 1) / 2) (-1)} : ℝ) := by sorry
