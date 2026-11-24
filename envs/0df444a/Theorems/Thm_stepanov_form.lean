-- Prove2me | Theorems.Thm_stepanov_form
-- name    : stepanov_form
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:34:20.796401+00:00
-- url     : https://prove2.me/theorems/aff5dafd-aa43-474a-ae50-7eaab581de7c
-- title:
--   Hasse differentiation preserves the Stepanov polynomial form
-- statement:
--   Over a finite field of size q, let k < ℓ and k < q. For R = f^ℓ Σⱼ<J(rⱼ + sⱼfᶜ)Xʲᑫ, there are polynomial families rⱼ,ₖ and sⱼ,ₖ such that Dₖ(f^ℓrⱼ) = rⱼ,ₖf^(ℓ−k), Dₖ(f^(ℓ+c)sⱼ) = sⱼ,ₖf^(ℓ+c−k), and DₖR = f^(ℓ−k)Σⱼ<J(rⱼ,ₖ + sⱼ,ₖfᶜ)Xʲᑫ.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovAuxiliary.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovAuxiliary.lean lines 286–459; SHA256 5c716bf363ff271afb18158456c5f40ab18777e3eafdb03903953fdbc5d982a8.

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

theorem stepanov_form (F : Type*) [Field F] [Fintype F]
    (f : Polynomial F) (ℓ q c J k : ℕ) (hk : k < ℓ)
    (hq : q = Fintype.card F) (hkq : k < q)
    (rj sj : ℕ → Polynomial F) :
  ∃ rjk sjk : ℕ → Polynomial F,
    (∀ j, hasseDerivOp F k (f^ℓ * (rj j)) = (rjk j) * f^(ℓ - k)) ∧
    (∀ j, hasseDerivOp F k (f^(ℓ + c) * (sj j)) = (sjk j) * f^(ℓ + c - k)) ∧
    hasseDerivOp F k
      (f^ℓ *
        (Finset.sum (Finset.range J)
          (fun j => ((rj j) + (sj j) * f^c) * (Polynomial.X)^(j*q)))) =
      f^(ℓ - k) *
        Finset.sum (Finset.range J)
          (fun j => ((rjk j) + (sjk j) * f^c) * (Polynomial.X)^(j*q)) := by sorry
