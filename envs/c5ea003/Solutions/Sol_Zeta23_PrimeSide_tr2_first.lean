-- Prove2me | solution 1 for Zeta23.PrimeSide.tr2_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:06:07.256943+00:00
-- url     : https://prove2.me/submissions/8ee93c48-f416-4df9-8e28-fe8f09dad5ff

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





/-- Weaken the majorant up to a constant: if `g ≤ c·g'` eventually then `EvBound f g → EvBound f g'`. -/
lemma mono_right' {f g g' : ℝ → ℝ} (h : EvBound f g) {c : ℝ} (hc : 0 < c)
    (hgg' : ∀ᶠ T in atTop, g T ≤ c * g' T) : EvBound f g' := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hgg'
  refine ⟨C * c, mul_pos hC hc, max T₀ T₁, fun T hT' => (hT T (le_of_max_le_left hT')).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hT₁ T (le_of_max_le_right hT')) hC.le

/-- An eventual pointwise bound with an explicit constant gives an `EvBound`. -/
lemma of_eventually_le {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ᶠ T in atTop, |f T| ≤ c * g T) : EvBound f g := by
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp h
  exact ⟨c, hc, T₀, hT₀⟩

lemma eventually_le {f g : ℝ → ℝ} (h : EvBound f g) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T in atTop, |f T| ≤ C * g T := by
  obtain ⟨C, hC, T₀, hT⟩ := h
  exact ⟨C, hC, eventually_atTop.mpr ⟨T₀, hT⟩⟩

lemma add {f₁ f₂ g : ℝ → ℝ} (h₁ : EvBound f₁ g) (h₂ : EvBound f₂ g) :
    EvBound (fun T => f₁ T + f₂ T) g := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁.eventually_le
  obtain ⟨C₂, hC₂, h₂⟩ := h₂.eventually_le
  refine of_eventually_le (add_pos hC₁ hC₂) ?_
  filter_upwards [h₁, h₂] with T a b
  calc |f₁ T + f₂ T| ≤ |f₁ T| + |f₂ T| := abs_add_le _ _
    _ ≤ C₁ * g T + C₂ * g T := add_le_add a b
    _ = (C₁ + C₂) * g T := by ring


lemma const_mul {f g : ℝ → ℝ} (h : EvBound f g) (c : ℝ) :
    EvBound (fun T => c * f T) g := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  refine of_eventually_le (mul_pos (by positivity : (0:ℝ) < |c| + 1) hC) ?_
  filter_upwards [h, h.mono (fun T hT => (abs_nonneg _).trans hT)] with T a b
  rw [abs_mul, mul_assoc]
  calc |c| * |f T| ≤ |c| * (C * g T) := mul_le_mul_of_nonneg_left a (abs_nonneg c)
    _ ≤ (|c| + 1) * (C * g T) := by nlinarith

/-- Change `f` up to eventual pointwise domination. -/
lemma of_abs_le {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, |f' T| ≤ |f T|) :
    EvBound f' g := by
  obtain ⟨C, hC, h⟩ := h.eventually_le
  refine of_eventually_le hC ?_
  filter_upwards [h, h'] with T a b using b.trans a

lemma congr_left {f f' g : ℝ → ℝ} (h : EvBound f g) (h' : ∀ᶠ T in atTop, f' T = f T) :
    EvBound f' g := h.of_abs_le (h'.mono fun T hT => by rw [hT])


end EvBound

/-! ## §1.  The scalar parameters of `Defs.lean` -/

namespace PaperParams

lemma l_tendsto_atTop : Tendsto l atTop atTop := by
  unfold l
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))





variable (P : Params)


/-- `X = (T/2π)^λ` for `T > 0`. -/
lemma X_eq_rpow {T : ℝ} (hT : 0 < T) : P.X T = (T / (2 * π)) ^ P.lam := by
  unfold Params.X Params.L l
  rw [Real.rpow_def_of_pos (div_pos hT (by positivity)), mul_comm]

lemma L_tendsto_atTop (hP : 0 < P.lam) : Tendsto P.L atTop atTop := by
  unfold Params.L
  exact l_tendsto_atTop.const_mul_atTop hP

lemma log_l_tendsto_atTop : Tendsto (fun T => Real.log (l T)) atTop atTop :=
  Real.tendsto_log_atTop.comp l_tendsto_atTop

lemma eventually_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ l T := l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_log_l_ge (c : ℝ) : ∀ᶠ T in atTop, c ≤ Real.log (l T) :=
  log_l_tendsto_atTop.eventually_ge_atTop c

lemma eventually_L_ge (hlam : 0 < P.lam) (c : ℝ) : ∀ᶠ T in atTop, c ≤ P.L T :=
  (L_tendsto_atTop P hlam).eventually_ge_atTop c



/-- `L ≤ l` when `λ ≤ 1` and `l ≥ 0`. -/
lemma L_le_l (hlam1 : P.lam ≤ 1) {T : ℝ} (hl : 0 ≤ l T) : P.L T ≤ l T := by
  unfold Params.L; nlinarith



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

lemma eventually_one_le_X (hlam : 0 < P.lam) : ∀ᶠ T in atTop, 1 ≤ P.X T := by
  filter_upwards [eventually_L_ge P hlam 0] with T hL
  simpa [Params.X] using Real.one_le_exp hL


variable {P}







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






/-- The common regime `T ≥ 1, l ≥ 1, log l ≥ 1, L ≥ 1, X ≥ 1, L ≤ l, X ≤ T` (eventually). -/
lemma regime : ∀ᶠ T in atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T) ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧
    P.L T ≤ l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1, eventually_one_le_X P hlam, eventually_X_le_T P hlam h.lam_le_one]
    with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, L_le_l P h.lam_le_one (by linarith), h6⟩







end assembly

end PrimeSide

/-! ## §3.  [prop:PP]

Statement over `Mform` and `Defs.lean`'s `PX, PhiR, g`,
via the 𝒟 / 𝒪₁ / 𝒪₂ decomposition [eq:MPP]. -/

end Zeta23

end
open Real Filter Asymptotics Topology
open Zeta23
open PrimeSide
open PaperParams
variable {P : Params} (D : Data P)
variable {D} (h : Facts D)
include h

theorem solution : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2g T))
    (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
  -- every secondary error term is ≤ R := L l log l (l² + X) in the regime
  have e3 : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_mumu.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    have hlogL : Real.log (P.L T) ≤ Real.log (l T) := Real.log_le_log (by linarith) hLl
    have hlogL0 : 0 ≤ Real.log (P.L T) := Real.log_nonneg hL
    calc l T ^ 2 * Real.log (P.L T) ≤ l T ^ 2 * Real.log (l T) := by gcongr
      _ = 1 * l T * Real.log (l T) * l T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e4 : EvBound (fun T => D.MPP T - T / π * D.sumL2g T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_PP.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T ^ 2 * P.X T = P.L T * P.L T * 1 * P.X T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have hsqrtX : ∀ᶠ T in atTop, Real.sqrt (P.X T) ≤ P.X T := by
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have e5 : EvBound D.MmuP (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muP.mono_right' one_pos ?_
    filter_upwards [regime h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * Real.sqrt (P.X T) ≤ l T * P.X T := by gcongr
      _ = 1 * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e6 : EvBound D.MmuPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muPi.mono_right' one_pos ?_
    filter_upwards [regime h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * P.L T * Real.sqrt (P.X T) ≤ l T * P.L T * P.X T := by gcongr
      _ = P.L T * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e7 : EvBound D.MPPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PPi.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have e8 : EvBound D.MPiPi (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_PiPi.mono_right' one_pos ?_
    filter_upwards [regime h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T * P.X T / T ≤ P.L T * P.X T := div_le_self (by nlinarith) hT
      _ = P.L T * 1 * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have S := h.lem_ends.add (e3.add (e4.add (((e5.const_mul 2).add (e6.const_mul 2)).add
    ((e7.const_mul 2).add e8))))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]; ring
