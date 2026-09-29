-- Prove2me | Definitions.Def_Zeta23_MV
-- name    : Zeta23_MV
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:06:51.82629+00:00
-- url     : https://prove2.me/theorems/0c7769fc-b8eb-4948-98c4-490c355243e8
-- title:
--   The diagonal Montgomery–Vaughan inequality $\mathrm{MVDiag}\,C$ and the sesquilinear Hilbert form
-- statement:
--   This bundle states the literature (diagonal) form of the Montgomery–Vaughan weighted Hilbert inequality as a proposition with an abstract constant, together with the sesquilinear form used to polarize it.
--
--   The central definition is `Zeta23.MVDiag C`, the proposition: for every finite index type $\iota$, all real frequencies $\lambda_r$ (`freq`, assumed injective) and admissible gaps $\delta_r$ ($0 < \delta_r \le |\lambda_r - \lambda_s|$ for all $s \neq r$), and all complex $x_r$,
--   $$\Bigl| \sum_{r \neq s} \frac{x_r \overline{x_s}}{\lambda_r - \lambda_s} \Bigr| \;\le\; C \sum_r \frac{|x_r|^2}{\delta_r}.$$
--   This is Montgomery–Vaughan (1974), Theorem 2, whose constant is $C = 3\pi/2$; the project keeps $C$ abstract since only $\exists C$ is needed. The helpers spell out the ingredients of the polarization argument: `MV.coef` is the coefficient $c_{rs} = (\lambda_r - \lambda_s)^{-1}$ for $r \neq s$ and $0$ on the diagonal; `MV.B` is the sesquilinear form $B(x,z) = \sum_{r,s} x_r \overline{z_s}\, c_{rs}$; and `MV.N2` is the weighted $\ell^2$ quantity $\sum_r |x_r|^2/\delta_r$.
--
--   Role: the surrounding module derives from `MVDiag C` the bilinear inequality `Zeta23.MVHilbert (2C)` (hypothesis H-MV of the project, [lem:MV]) by polarization and rescaling — the form actually consumed by [prop:PP] and [prop:cross] on the prime side. `MVDiag` is in turn proved unconditionally in the `Zeta23.MV` chain (Spacing, Quadratic, Eigen, Duality), removing Montgomery–Vaughan from the trust base.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/MV.lean, docstring tag [lem:MV]

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

/-- **MV74 Theorem 2 (weighted Hilbert inequality), literature = diagonal form**, with an
abstract absolute constant C (MV74: C = 3π/2): for distinct real frequencies λ_r and admissible
gaps δ_r (0 < δ_r ≤ |λ_r − λ_s| for all s ≠ r), and all complex x_r,
  |Σ_{r≠s} x_r x̄_s/(λ_r − λ_s)| ≤ C · Σ_r |x_r|²/δ_r.
Same binder shape as Zeta23.MVHilbert with z := x. -/
def MVDiag (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (x s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * ∑ r, ‖x r‖ ^ 2 / δ r

namespace MV

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sesquilinear form B(x,z) := Σ_{r≠s} x_r z̄_s/(λ_r−λ_s), written with a coefficient
c_{rs} (0 on the diagonal) so that (bi)linearity is by ring. -/
def coef (freq : ι → ℝ) (r s : ι) : ℂ :=
  if r = s then 0 else (((freq r - freq s : ℝ) : ℂ))⁻¹

def B (freq : ι → ℝ) (x z : ι → ℂ) : ℂ := ∑ r, ∑ s, x r * conj (z s) * coef freq r s

/-- the weighted ℓ² quantity Σ |x_r|²/δ_r. -/
def N2 (δ : ι → ℝ) (x : ι → ℂ) : ℝ := ∑ r, ‖x r‖ ^ 2 / δ r













end MV



end Zeta23


