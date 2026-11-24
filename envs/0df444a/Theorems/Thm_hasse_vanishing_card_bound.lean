-- Prove2me | Theorems.Thm_hasse_vanishing_card_bound
-- name    : hasse_vanishing_card_bound
-- status  : Proved
-- author  : @yousofy
-- created : 2026-11-24T14:18:29.622142+00:00
-- url     : https://prove2.me/theorems/2ed11e55-0f25-456a-84cf-3fb6933e658a
-- title:
--   A multiplicity-weighted bound for a finite zero set
-- statement:
--   Let r be a nonzero polynomial over a field, let ℓ > 0, and let S be a finite set. If every Hasse derivative of r of order below ℓ vanishes at every point of S, then |S| ≤ natDegree(r)/ℓ as a real inequality.
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/RiemannHypothesisHEC.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/RiemannHypothesisHEC.lean lines 7–61; SHA256 38a0ced50a32a24472c5b0424d467d223fd61271d92d6f506409fb4af6bf75cc.

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

theorem hasse_vanishing_card_bound
  (F : Type*) [Field F] [DecidableEq F]
  (r : Polynomial F) (ℓ : ℕ)
  (S : Finset F)
  (hr : r ≠ 0)
  (hℓ_pos : 0 < ℓ)
  (hvan : ∀ x ∈ S, ∀ k < ℓ, (hasseDerivOp F k r).eval x = 0) :
  (S.card : ℝ) ≤ (r.natDegree : ℝ) / ℓ := by sorry
