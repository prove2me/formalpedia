-- Prove2me | Theorems.Thm_curve_count_ge_two_times_N1
-- name    : curve_count_ge_two_times_N1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:18.290067+00:00
-- url     : https://prove2.me/theorems/4fa7c9fe-4a4d-4d9c-a444-068d40add24c
-- title:
--   Nonzero quadratic residues contribute two affine curve points
-- statement:
--   Over a finite field F of odd characteristic and size q, the number of affine solutions of y² = f(x) is at least twice the number of x for which f(x) ≠ 0 and f(x)^((q−1)/2) = 1.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 364–482; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

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

theorem curve_count_ge_two_times_N1
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (f : Polynomial F) (q : ℕ)
    (hq : q = Fintype.card F)
    (hodd : ringChar F ≠ 2) :
    (Fintype.card {p : F × F // p.2 ^ 2 = Polynomial.eval p.1 f} : ℝ)
      ≥
        2 *
          (Fintype.card
              {x : F // (Polynomial.eval x f) ^ ((q - 1) / 2) = 1 ∧
                Polynomial.eval x f ≠ 0} : ℝ) := by sorry
