-- Prove2me | solution 1 for Zeta23.MVHilbert_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:18:19.842753+00:00
-- url     : https://prove2.me/submissions/17870d8a-0cfc-4c87-a3e6-32b7a30886e9

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_MV
import Theorems.Thm_Zeta23_MV_norm_B_le_sqrt

-- from Zeta23.MV
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/MV.lean — the Montgomery–Vaughan weighted Hilbert inequality: literature (diagonal, y = x)
form ⇒ the bilinear (x, z) form H-MV of Zeta23/Hypotheses.lean.

Purpose (trust reduction): Zeta23.MVHilbert C — what [prop:PP]/[prop:cross] consume —
is the BILINEAR inequality |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ C (Σ|x_r|²/δ_r)^{1/2} (Σ|z_r|²/δ_r)^{1/2}.
The published theorem is the case z = x.  The paper, [lem:MV] and its proof,
verbatim: "Lemma (Montgomery–Vaughan). Let λ_1,…,λ_R be distinct real numbers and
δ_r := min_{s≠r}|λ_r−λ_s|. Then for all complex x_r, z_r,
  |Σ_{r≠s} x_r z̄_s/(λ_r−λ_s)| ≤ (3π/2)(Σ_r |x_r|²/δ_r)^{1/2}(Σ_r |z_r|²/δ_r)^{1/2}.
Proof. For z = x this is the weighted ("generalised") Hilbert inequality of Montgomery and Vaughan
[MV74, Theorem 2]; see also [Mon94, Chapter 7]. Any absolute constant in place of 3π/2 would
suffice below. In general, let H be the Hermitian matrix with entries i/(λ_r−λ_s) off the
diagonal and 0 on it, and Δ := diag(δ_r^{1/2}). The case z = x says |y*(ΔHΔ)y| ≤ (3π/2)‖y‖₂² for
all y, i.e. ‖ΔHΔ‖ ≤ 3π/2 since ΔHΔ is Hermitian; hence
|x*Hz| = |(Δ⁻¹x)*(ΔHΔ)(Δ⁻¹z)| ≤ (3π/2)‖Δ⁻¹x‖₂‖Δ⁻¹z‖₂."

Literature statement transcribed (H. L. Montgomery and R. C. Vaughan, "Hilbert's inequality",
J. London Math. Soc. (2) 8 (1974), 73–82, Theorem 2 = the "generalised" weighted form, their
(1.8)): if λ_1,…,λ_R are distinct reals, δ_r := min_{s≠r}|λ_r − λ_s|, then for all complex x_r,
  |Σ_{r≠s} x_r x̄_s / (λ_r − λ_s)| ≤ (3π/2) Σ_r |x_r|²/δ_r.
(The constant 3π/2 was later improved — Preissmann 1984 — but the paper says any absolute
constant suffices, and the headline result only needs ∃ C, so C is kept abstract: MVDiag C.)
As in Zeta23.MVHilbert we allow any admissible δ (δ_r > 0, δ_r ≤ |λ_r − λ_s| for s ≠ r); the right
side is antitone in δ, so this is equivalent to the min-gap δ of the literature.

We derive the bilinear form with constant 2C (not C) by POLARIZATION of the sesquilinear form plus
the scaling x ↦ t x, z ↦ z/t — an elementary route that avoids operator norms; the factor 2 is
immaterial (∃ C).  Result: Zeta23.MVHilbert_of_diag : 0 ≤ C → MVDiag C → MVHilbert (2 * C), and
Zeta23.exists_MVHilbert_of_diag for the ∃-forms used by PaperInputs.MV.
-/

noncomputable section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Zeta23


namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]




lemma sum_eq_B (freq : ι → ℝ) (x z : ι → ℂ) :
    (∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ))
      = B freq x z := by
  unfold B coef
  refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
  split_ifs <;> simp [div_eq_mul_inv]












end MV



end Zeta23
end
open Finset Complex
open scoped BigOperators ComplexConjugate
open Zeta23

theorem solution {C : ℝ} (hC : 0 ≤ C) (h : MVDiag C) : MVHilbert (2 * C) := by
  intro ι _ _ freq δ x z hinj hδ hsep
  rw [MV.sum_eq_B]
  have hdiag : ∀ y : ι → ℂ, ‖MV.B freq y y‖ ≤ C * MV.N2 δ y := by
    intro y
    have := h ι freq δ y hinj hδ hsep
    rw [MV.sum_eq_B] at this
    exact this
  exact MV.norm_B_le_sqrt hC hδ hdiag x z
