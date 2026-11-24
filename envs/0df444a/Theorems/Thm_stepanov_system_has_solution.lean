-- Prove2me | Theorems.Thm_stepanov_system_has_solution
-- name    : stepanov_system_has_solution
-- status  : Open
-- author  : @yousofy
-- created : 2026-11-24T15:35:50.139583+00:00
-- url     : https://prove2.me/theorems/2b2c410b-600b-425c-b6cf-ea6042c45afc
-- title:
--   The Stepanov linear system has a nontrivial bounded-degree solution
-- statement:
--   Let F be a finite field of size q and f have degree m ≥ 2. Suppose q > 6m and 0 < ℓ ≤ q/3. Set c = (q−1)/2, d = ⌈(q−m)/2⌉−1, and J = ⌈ℓ/2+ℓ²m/q⌉, with J ≥ 1. For each a ∈ F there are families rⱼ,sⱼ of degree at most d for j < J, not all zero, such that for every k < ℓ and every nonzero-value point f(x)ᶜ = a, Σⱼ<J[Q_{ℓ,k}(rⱼ)(x)+aQ_{ℓ+c,k}(sⱼ)(x)]xʲ = 0. Here Q_{r,k}(p) = Dₖ(fʳp)/f^(r−k).
-- source:
--   Ported from https://github.com/math-inc/RiemannHypothesisCurves/blob/c99880dff2a087d59147ab832074379ac28f7e68/RiemannHypothesisCurves/StepanovSystem.lean; checked task source research/hec-lean433/RiemannHypothesisCurves/StepanovSystem.lean lines 763–1001; SHA256 8598e8f2f5a5feb4a726f52cf8cda87aea55e087771de3eb377b792d7c6081ff.

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

theorem stepanov_system_has_solution
  (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (q m ℓ : ℕ) (a : F)
  (_hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hm_ge_two : 2 ≤ m) (_hm_pos : 0 < m) (hℓ_pos : 0 < ℓ)
  (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
  (hJ_pos :
      1 ≤ Nat.ceil (((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))) :
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  let J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  ∃ rj sj : ℕ → Polynomial F,
    (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
    (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
    (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ ((q - 1) / 2) = a →
      ∀ k < ℓ,
        Finset.sum (Finset.range J)
          (fun j =>
            (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
              a *
                ((hasseDerivOp F k (f ^ (ℓ + ((q - 1) / 2)) * sj j)) /
                    f ^ (ℓ + ((q - 1) / 2) - k)).eval x) *
              x ^ j) = 0) := by sorry
