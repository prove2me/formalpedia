-- Prove2me | Theorems.Thm_stepanov_vanishing_nonzeros
-- name    : stepanov_vanishing_nonzeros
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:35:48.981183+00:00
-- url     : https://prove2.me/theorems/e1e6b9f1-b290-4785-9b4a-d516b6d0a0db
-- title:
--   Quotient constraints imply Hasse vanishing at nonroot points
-- statement:
--   Over a finite field of size q, let R = f^ℓΣⱼ<J(rⱼ+sⱼfᶜ)Xʲᑫ and suppose every k < ℓ also satisfies k < q. Fix x with f(x) ≠ 0 and f(x)ᶜ = a. If Σⱼ<J[Q_{ℓ,k}(rⱼ)(x)+aQ_{ℓ+c,k}(sⱼ)(x)]xʲ = 0 for every k < ℓ, where Q_{r,k}(p) = Dₖ(fʳp)/f^(r−k), then DₖR(x) = 0 for every k < ℓ.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovVanishing.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovVanishing.lean lines 12–58; SHA256 d38fa30d1cd29d1d17c163f10bf9882a943be13aeb9bdc9eba90ef005549b832.

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

theorem stepanov_vanishing_nonzeros (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (ℓ q c J : ℕ) (hq : q = Fintype.card F)
  (rj sj : ℕ → Polynomial F) (a x : F) (hkq : ∀ k < ℓ, k < q) (hvan :
    ∀ k < ℓ,
    Finset.sum (Finset.range J)
      (fun j =>
        (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x
          + a *
            ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) / f ^ (ℓ + c - k)).eval x) *
          x ^ j) = 0)
  (hx_ne : f.eval x ≠ 0) (hx_pow : (f.eval x) ^ c = a) :
  ∀ k < ℓ,
  (hasseDerivOp F k
    (f ^ ℓ * (Finset.sum (Finset.range J)
      (fun j => ((rj j) + (sj j) * f ^ c) * Polynomial.X ^ (j * q))))).eval x = 0 := by sorry
