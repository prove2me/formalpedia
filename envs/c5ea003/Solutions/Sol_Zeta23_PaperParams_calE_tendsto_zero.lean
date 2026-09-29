-- Prove2me | solution 1 for Zeta23.PaperParams.calE_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:55:16.061028+00:00
-- url     : https://prove2.me/submissions/916a0b91-d046-4b97-9b9a-4cb0a8d4568f

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideTemp

-- from Zeta23.PrimeSideB
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Prime side, part B: [prop:PP] and the assembly of Theorem [thm:traces]

Paper §5 ("The prime side: magnitude"), subsections "Evaluation of 𝓜" and "Summary".

Contents
* §0 glue between the explicit-constant interface shape `EvBound` and Mathlib's `IsBigO`.
* §1 `Zeta23.PaperParams`: elementary facts about the scalar parameters `l, ℓ₁, L, X, λ₁, 𝓔_T`
  of `Defs.lean` (growth, positivity, `𝓔_T → 0`).  Pure real analysis, no hypotheses.
* §2 `Zeta23.PrimeSide.Facts` / `Zeta23.PrimeSide.tracesBounds_of_facts`: the proof of [thm:traces]
  ([eq:tr1], [eq:tr2], [eq:ratio], second forms) from the five sub-results of §5 + [eq:muints] (H-Γ)
  + [eq:RvM] (H-RvM) + [eq:abdef] (Taper), all taken as hypotheses on abstract real functions of `T`.
  This is where the paper's constants `ℓ₁² + L²/3` and `F(λ₁)` are checked.
* §3 [prop:PP]: `𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L² X)` and the sandwich
  `(L−2w)³/6 + O(L²) ≤ Σ a_n² g(y_n) ≤ L³/6 + O(L²)` — over the concrete definitions of `Defs.lean`
  and `Mform`.
-/

noncomputable section

open Real Filter Asymptotics Topology

namespace Zeta23

/-! ## §0.  Explicit-constant ↔ `IsBigO` glue -/

namespace EvBound














end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams

lemma l_tendsto_atTop : Tendsto l atTop atTop := by
  unfold l
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))





variable (P : Params)

lemma X_pos (T : ℝ) : 0 < P.X T := Real.exp_pos _

/-- `X = (T/2π)^λ` for `T > 0`. -/
lemma X_eq_rpow {T : ℝ} (hT : 0 < T) : P.X T = (T / (2 * π)) ^ P.lam := by
  unfold Params.X Params.L l
  rw [Real.rpow_def_of_pos (div_pos hT (by positivity)), mul_comm]

lemma L_tendsto_atTop (hP : 0 < P.lam) : Tendsto P.L atTop atTop := by
  unfold Params.L
  exact l_tendsto_atTop.const_mul_atTop hP


lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c








/-- `X ≤ T` eventually (`λ ≤ 1`). -/
lemma eventually_X_le_T (_hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) : ∀ᶠ T in atTop, P.X T ≤ T := by
  filter_upwards [eventually_ge_atTop (2 * π)] with T hT
  have hπ := Real.pi_gt_three
  have hT0 : 0 < T := by linarith
  rw [X_eq_rpow P hT0]
  have h1 : 1 ≤ T / (2 * π) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc (T / (2 * π)) ^ P.lam ≤ (T / (2 * π)) ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hlam1
    _ = T / (2 * π) := Real.rpow_one _
    _ ≤ T := by rw [div_le_iff₀ (by positivity)]; nlinarith



variable {P}

/-- each of the three summands of `𝓔_T` is eventually nonnegative -/
lemma calE_summands_nonneg (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.w / P.L T ∧
      0 ≤ (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T) ∧ 0 ≤ T ^ (P.lam / 2 - 1) := by
  filter_upwards [(L_tendsto_atTop P hlam).eventually_ge_atTop 0,
    l_tendsto_atTop.eventually_ge_atTop 1, eventually_ge_atTop (0:ℝ)] with T hL hl hT
  refine ⟨div_nonneg hw hL, div_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (X_pos P T).le)
    (Real.log_nonneg hl)) (mul_nonneg hT (by linarith)), Real.rpow_nonneg hT _⟩




lemma calE_nonneg_eventually (hlam : 0 < P.lam) (hw : 0 ≤ P.w) :
    ∀ᶠ T in atTop, 0 ≤ P.calE T := by
  filter_upwards [calE_summands_nonneg hlam hw] with T ⟨h1, h2, h3⟩
  unfold Params.calE; linarith


end PaperParams

/-! ## §2.  Assembly of Theorem [thm:traces] from the §5 sub-results

All quantities are real functions of `T` at fixed `P = (ϱ, λ, w)`.  The hypotheses below are exactly
the conclusions of [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:PP], [prop:cross]
(the paper §5), [eq:muints] (from H-Γ), [eq:RvM] (H-RvM) and [eq:abdef] (Taper), each in the
explicit-constant form `EvBound`. -/

namespace PrimeSide

open PaperParams


variable {P : Params} (D : Data P)


/-! ### The assembly -/

section assembly
variable {D} (h : Facts D)
include h













end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end
open Real Filter Asymptotics Topology
open Zeta23
open PaperParams
variable (P : Params)
variable {P}

theorem solution (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by
  -- w / L → 0
  have h1 : Tendsto (fun T => P.w / P.L T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (L_tendsto_atTop P hlam)
  -- T^{λ/2 - 1} → 0
  have h3 : Tendsto (fun T : ℝ => T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    have : P.lam / 2 - 1 = -(1 - P.lam / 2) := by ring
    rw [this]; exact tendsto_rpow_neg_atTop (by linarith)
  -- l² / T → 0
  have h2a : Tendsto (fun T => l T ^ 2 / T) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop (2 * π) 0 2 (by positivity)).comp
      (tendsto_id.atTop_div_const (show (0:ℝ) < 2 * π by positivity))
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    simp only [Function.comp, l, id, add_zero]
    rw [mul_div_cancel₀ _ (by positivity)]
  -- log l / l → 0
  have h2b : Tendsto (fun T => Real.log (l T) / l T) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp l_tendsto_atTop
    simpa [Function.comp_def] using this
  have hsum : Tendsto (fun T => P.w / P.L T + (l T ^ 2 / T + Real.log (l T) / l T)
      + T ^ (P.lam / 2 - 1)) atTop (𝓝 0) := by
    simpa using (h1.add (h2a.add h2b)).add h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (calE_nonneg_eventually hlam hw) ?_
  filter_upwards [eventually_l_ge 1, eventually_X_le_T P hlam hlam1, eventually_ge_atTop 1]
    with T hl hXT hT
  unfold Params.calE
  have hlog0 : 0 ≤ Real.log (l T) := Real.log_nonneg hl
  have hlogle : Real.log (l T) ≤ l T := Real.log_le_self (by linarith)
  have hX0 : 0 ≤ P.X T := (X_pos P T).le
  have hl0 : 0 < l T := by linarith only [hl]
  have hT0 : 0 < T := by linarith only [hT]
  have e1 : l T ^ 2 * Real.log (l T) / (T * l T) ≤ l T ^ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith only [hlogle, mul_nonneg (sq_nonneg (l T)) hT0.le]
  have e2 : P.X T * Real.log (l T) / (T * l T) ≤ Real.log (l T) / l T := by
    rw [div_le_div_iff₀ (by positivity) hl0]
    nlinarith only [hXT, mul_nonneg hlog0 hl0.le]
  have e3 : (l T ^ 2 + P.X T) * Real.log (l T) / (T * l T)
      = l T ^ 2 * Real.log (l T) / (T * l T) + P.X T * Real.log (l T) / (T * l T) := by ring
  linarith only [e1, e2, e3]
