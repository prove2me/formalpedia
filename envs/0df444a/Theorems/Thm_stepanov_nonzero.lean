-- Prove2me | Theorems.Thm_stepanov_nonzero
-- name    : stepanov_nonzero
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T15:34:19.786911+00:00
-- url     : https://prove2.me/theorems/c8b12d93-6cea-4f75-a69a-66a9923bbc65
-- title:
--   The Stepanov coefficient parameterization is injective
-- statement:
--   Let F be an odd finite field of size q and f a polynomial of positive degree m with q > 6m, nonsquare over the algebraic closure. Put c = (q−1)/2 and d = ⌈(q−m)/2⌉−1. For coefficient polynomials of degree at most d, f^ℓΣⱼ<J(rⱼ+sⱼfᶜ)Xʲᑫ is zero exactly when all rⱼ and sⱼ for j < J are zero.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovNonSquare.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovNonSquare.lean lines 549–873; SHA256 c068582a3c56d317a522c43afeafce6091ae371a22640b79e14df39de7a6fa88.

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

theorem stepanov_nonzero (F : Type*) [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (f : Polynomial F) (q m ℓ J c : ℕ) (hc : c = (q - 1) / 2)
    (hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
    (hm_pos : 0 < m)
    (hq6m : q > 6 * m)
    (rj sj : ℕ → Polynomial F)
    (hnsq : ¬ ∃ g : Polynomial (AlgebraicClosure F),
      g * g = Polynomial.map (algebraMap F (AlgebraicClosure F)) f)
    (hdeg : ∀ j < J, (rj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1 ∧
                     (sj j).natDegree ≤ Nat.ceil (((q : ℚ) - m) / 2) - 1) :
  (f ^ ℓ *
      (Finset.sum (Finset.range J)
        (fun j => ((rj j) + (sj j) * f ^ c) * (Polynomial.X) ^ (j * q)))) = 0 ↔
    (∀ j < J, rj j = 0 ∧ sj j = 0) := by sorry
