-- Prove2me | solution 1 for shefferExpr_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:03:52.010258+00:00
-- url     : https://prove2.me/submissions/4dac5db3-0c5b-4807-8d4f-945dce03d9af

-- Sol generated from MachineLearning/ShefferFunction/Lean/ShefferFoundations.lean
import Mathlib
import Definitions.Def_MachineLearning_ShefferFunction_Lean_ShefferAlgebra
import Theorems.Thm_softplus_abs_sub_le

/-!
# The Lipschitz barrier for the Sheffer algebra

`ExtendedTheorems.lean` is written against three upstream modules that are absent from this
repository (`ShefferAI.Lean.UniversalApproximation`, `.FutureTheorems`, `.AdvancedTheorems`,
`.NewTheorems`).  The results it actually uses from them are the closure of the Sheffer
algebra under scalar multiplication and the exclusion of `x²`.  This file supplies both,
from scratch.

The exclusion of `x²` is the **Lipschitz barrier**: every Sheffer expression is globally
Lipschitz, because the only nonlinear building block, softplus, is `1`-Lipschitz and the
three closure operations (affine pre-composition, affine combination, composition) all
preserve global Lipschitz continuity.  Since `x ↦ x²` is not globally Lipschitz on `ℝ`, it
is not in the algebra — and hence the algebra is not closed under pointwise multiplication.
-/

open Real

noncomputable section






theorem solution(e : ShefferExpr) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, |e.eval x - e.eval y| ≤ C * |x - y| := by
  induction e with
  | base =>
      exact ⟨1, zero_le_one, fun x y => by simpa using softplus_abs_sub_le x y⟩
  | affine_pre a b e ih =>
      obtain ⟨C, hC, h⟩ := ih
      refine ⟨C * |a|, by positivity, fun x y => ?_⟩
      have hstep := h (a * x + b) (a * y + b)
      have harg : |a * x + b - (a * y + b)| = |a| * |x - y| := by
        rw [show a * x + b - (a * y + b) = a * (x - y) by ring, abs_mul]
      simp only [ShefferExpr.eval]
      calc |e.eval (a * x + b) - e.eval (a * y + b)| ≤ C * |a * x + b - (a * y + b)| := hstep
        _ = C * |a| * |x - y| := by rw [harg]; ring
  | affine_comb α β γ e₁ e₂ ih₁ ih₂ =>
      obtain ⟨C₁, hC₁, h₁⟩ := ih₁
      obtain ⟨C₂, hC₂, h₂⟩ := ih₂
      refine ⟨|α| * C₁ + |β| * C₂, by positivity, fun x y => ?_⟩
      have hd : α * e₁.eval x + β * e₂.eval x + γ - (α * e₁.eval y + β * e₂.eval y + γ)
          = α * (e₁.eval x - e₁.eval y) + β * (e₂.eval x - e₂.eval y) := by ring
      have hax : |α * (e₁.eval x - e₁.eval y)| = |α| * |e₁.eval x - e₁.eval y| := abs_mul _ _
      have hbx : |β * (e₂.eval x - e₂.eval y)| = |β| * |e₂.eval x - e₂.eval y| := abs_mul _ _
      have h1 := h₁ x y
      have h2 := h₂ x y
      simp only [ShefferExpr.eval]
      calc |α * e₁.eval x + β * e₂.eval x + γ - (α * e₁.eval y + β * e₂.eval y + γ)|
          = |α * (e₁.eval x - e₁.eval y) + β * (e₂.eval x - e₂.eval y)| := by rw [hd]
        _ ≤ |α * (e₁.eval x - e₁.eval y)| + |β * (e₂.eval x - e₂.eval y)| := abs_add_le _ _
        _ = |α| * |e₁.eval x - e₁.eval y| + |β| * |e₂.eval x - e₂.eval y| := by rw [hax, hbx]
        _ ≤ (|α| * C₁ + |β| * C₂) * |x - y| := by
            have ha : (0 : ℝ) ≤ |α| := abs_nonneg α
            have hb : (0 : ℝ) ≤ |β| := abs_nonneg β
            nlinarith [abs_nonneg (x - y)]
  | comp e₁ e₂ ih₁ ih₂ =>
      obtain ⟨C₁, hC₁, h₁⟩ := ih₁
      obtain ⟨C₂, hC₂, h₂⟩ := ih₂
      refine ⟨C₁ * C₂, by positivity, fun x y => ?_⟩
      have hstep := h₁ (e₂.eval x) (e₂.eval y)
      have h2 := h₂ x y
      simp only [ShefferExpr.eval]
      calc |e₁.eval (e₂.eval x) - e₁.eval (e₂.eval y)| ≤ C₁ * |e₂.eval x - e₂.eval y| := hstep
        _ ≤ C₁ * (C₂ * |x - y|) := by nlinarith
        _ = C₁ * C₂ * |x - y| := by ring
