-- Prove2me | solution 1 for Zeta23.PrimeSide.ratio_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:08:07.245023+00:00
-- url     : https://prove2.me/submissions/bcefaf69-faf6-4461-a1c5-4fc09986a402

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






variable (P : Params)
















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
omit h

theorem solution (T L ℓ lT E N G G2 A C₁ C₂ : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hℓ1 : 1 ≤ ℓ) (hℓl : lT ≤ ℓ) (hN0 : 0 < N) (hE0 : 0 ≤ E)
    (hET : 1 / T ≤ E) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hs1 : C₁ * E ≤ 1 / 2) (hs2 : C₂ * E ≤ 1 / 2) (hTA : 2 * π * A ≤ T)
    (h1 : |G - L * N| ≤ C₁ * (E * (L * N)))
    (h2 : |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)| ≤ C₂ * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))))
    (hN : |N - T * ℓ / (2 * π)| ≤ A * lT) :
    |G ^ 2 / G2 - Ffun (L / ℓ) * N| ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * (Ffun (L / ℓ) * N)) := by
  have hπ : 0 < π := Real.pi_pos
  have hT0 : 0 < T := by linarith only [hT]
  have hℓ0 : 0 < ℓ := by linarith only [hℓ1]
  set M₂ := T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3) with hM₂def
  have hM0 : 0 < M₂ := by positivity
  set Φ₀ := Ffun (L / ℓ) * N with hΦ₀def
  have hF0 : 0 < Ffun (L / ℓ) := by unfold Ffun; positivity
  have hΦ0 : 0 < Φ₀ := mul_pos hF0 hN0
  have key : Φ₀ * M₂ = L ^ 2 * N * (T * ℓ / (2 * π)) := by
    simp only [hΦ₀def, hM₂def, Ffun]
    field_simp
  set a := G - L * N with hadef
  set bb := G2 - M₂ with hbbdef
  set δ := N - T * ℓ / (2 * π) with hδdef
  have hbb : |bb| ≤ C₂ * (E * M₂) := h2
  have hG2low : M₂ / 2 ≤ G2 := by
    have : -(C₂ * (E * M₂)) ≤ bb := (abs_le.mp hbb).1
    have : C₂ * (E * M₂) ≤ 1 / 2 * M₂ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hs2 hM0.le
    linarith only [‹-(C₂ * (E * M₂)) ≤ bb›, this, hbbdef]
  have hG2pos : 0 < G2 := lt_of_lt_of_le (by positivity) hG2low
  -- the algebraic identity
  have hid : G ^ 2 - Φ₀ * G2 = L ^ 2 * N * δ + 2 * (L * N) * a + a ^ 2 - Φ₀ * bb := by
    have hG : G = L * N + a := by rw [hadef]; ring
    have hG2 : G2 = M₂ + bb := by rw [hbbdef]; ring
    rw [hG, hG2, hδdef]
    linear_combination (-1 : ℝ) * key
  -- (L N)² ≤ 2 Φ₀ M₂
  have hLN0 : 0 ≤ L * N := by positivity
  have hNup : N ≤ T * ℓ / (2 * π) + A * ℓ := by
    have := (abs_le.mp hN).2
    nlinarith only [this, hℓl, hA]
  have hLN2 : (L * N) ^ 2 ≤ 2 * (Φ₀ * M₂) := by
    rw [key]
    have h' : (L * N) ^ 2 = L ^ 2 * N * N := by ring
    rw [h']
    have hc : L ^ 2 * N * N ≤ L ^ 2 * N * (T * ℓ / (2 * π) + A * ℓ) :=
      mul_le_mul_of_nonneg_left hNup (by positivity)
    have hd : L ^ 2 * N * (A * ℓ) ≤ L ^ 2 * N * (T * ℓ / (2 * π)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hTA, hℓ0, hA]
    nlinarith only [hc, hd]
  -- the four bounds
  have t1 : |L ^ 2 * N * δ| ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ L ^ 2 * N)]
    calc L ^ 2 * N * |δ| ≤ L ^ 2 * N * (A * ℓ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hN.trans (mul_le_mul_of_nonneg_left hℓl hA)
      _ = 2 * π * A * ((1 / T) * (Φ₀ * M₂)) := by rw [key]; field_simp
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) := by gcongr
  have t2 : |2 * (L * N) * a| ≤ 4 * C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (L * N))]
    calc 2 * (L * N) * |a| ≤ 2 * (L * N) * (C₁ * (E * (L * N))) := by gcongr
      _ = 2 * C₁ * E * (L * N) ^ 2 := by ring
      _ ≤ 2 * C₁ * E * (2 * (Φ₀ * M₂)) := by gcongr
      _ = 4 * C₁ * (E * (Φ₀ * M₂)) := by ring
  have t3 : |a ^ 2| ≤ C₁ * (E * (Φ₀ * M₂)) := by
    rw [abs_pow]
    calc |a| ^ 2 ≤ (C₁ * (E * (L * N))) ^ 2 := by gcongr
      _ = (C₁ * E) * (C₁ * E) * (L * N) ^ 2 := by ring
      _ ≤ (C₁ * E) * (1 / 2) * (2 * (Φ₀ * M₂)) := by gcongr
      _ = C₁ * (E * (Φ₀ * M₂)) := by ring
  have t4 : |Φ₀ * bb| ≤ C₂ * (E * (Φ₀ * M₂)) := by
    rw [abs_mul, abs_of_pos hΦ0]
    calc Φ₀ * |bb| ≤ Φ₀ * (C₂ * (E * M₂)) := by gcongr
      _ = C₂ * (E * (Φ₀ * M₂)) := by ring
  have hnum : |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by
    rw [hid]
    calc |L ^ 2 * N * δ + 2 * (L * N) * a + a ^ 2 - Φ₀ * bb|
        ≤ |L ^ 2 * N * δ| + |2 * (L * N) * a| + |a ^ 2| + |Φ₀ * bb| := by
          refine (abs_sub _ _).trans ?_
          linarith only [abs_add_three (L ^ 2 * N * δ) (2 * (L * N) * a) (a ^ 2)]
      _ ≤ 2 * π * A * (E * (Φ₀ * M₂)) + 4 * C₁ * (E * (Φ₀ * M₂)) + C₁ * (E * (Φ₀ * M₂))
          + C₂ * (E * (Φ₀ * M₂)) := by gcongr
      _ = (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := by ring
  -- divide by G2 ≥ M₂/2
  have hq : G ^ 2 / G2 - Φ₀ = (G ^ 2 - Φ₀ * G2) / G2 := by
    field_simp
  rw [hq, abs_div, abs_of_pos hG2pos, div_le_iff₀ hG2pos]
  calc |G ^ 2 - Φ₀ * G2| ≤ (2 * π * A + 5 * C₁ + C₂) * (E * (Φ₀ * M₂)) := hnum
    _ = 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * (M₂ / 2) := by ring
    _ ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * Φ₀) * G2 := by gcongr
