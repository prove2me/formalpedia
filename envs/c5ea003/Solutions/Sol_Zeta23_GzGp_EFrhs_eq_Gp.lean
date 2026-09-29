-- Prove2me | solution 1 for Zeta23.GzGp.EFrhs_eq_Gp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:45:51.199099+00:00
-- url     : https://prove2.me/submissions/9df42f67-09b3-4eb5-b063-423710d8f6c0

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_GzGp_phiHat_conj

-- from Zeta23.Hypotheses.GzGp
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses/GzGp.lean — the H-EF bridge between the two expressions of [eq:Gdef]:  Z.Gz P T (zero side, Σ_ρ m_ρ φ̂(γ_ρ−τ_k)φ̂(γ_ρ−τ_l))
                  = P.Gp T  (prime side, ∫ φ̂(τ−τ_k)φ̂(τ−τ_l)ν_X(τ)dτ),
"the two expressions agreeing by Proposition [prop:EF]" — here: by hypothesis H-EF applied to
f = f_k, g = f_l, using h_{f_k}(z) = φ̂(z − τ_k) and "since φ̂ is real on ℝ we have
conj φ̂(conj z) = φ̂(z)" ([subsec:family] after [eq:fk]).
What this does and does not test: it checks the paper's internal consistency between [eq:Wdef],
[eq:fk], [eq:Gdef] and the form of [eq:EF] (conjugations, shifts, realness, support, X = e^L);
it does not test the 2π/sign normalisation inside ν_X, because [eq:EF] enters as the hypothesis
H-EF in the paper's own form — that normalisation is tested in Zeta23/ExplicitFormula.lean
(literature form ⇒ ExplicitFormulaPaper).
Taper regularity (φ ∈ C², supp φ ⊆ [−L/2, L/2]; Zeta23/Taper.lean) enters as
hypotheses. Helper lemmas are namespaced Zeta23.GzGp to avoid clashing with Zeta23/Taper.lean's
Params.phiHat_conj / Params.phiHat_ofReal (same statements; proved here independently so
this file depends only on Zeta23.Hypotheses).
-/

open scoped ComplexConjugate
open Complex MeasureTheory Set

noncomputable section

namespace Zeta23

namespace GzGp

variable (P : Params) (T : ℝ)



/-- h_{f_k}(z) = φ̂(z − τ_k)  ([subsec:family] after [eq:fk]). -/
lemma paperFT_fk (k : ℤ) (z : ℂ) : paperFT (P.fk T k) z = P.phiHat T (z - P.tau T k) := by
  unfold paperFT Params.phiHat Params.fk paperFT
  congr 1
  ext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring


/-- φ̂ is real on the real axis: φ̂(r) = φ̂_ℝ(r). -/
lemma phiHat_ofReal (r : ℝ) : P.phiHat T r = (P.phiHatR T r : ℂ) := by
  have h := phiHat_conj P T (r : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (P.phiHat T r).im = 0 := Complex.conj_eq_iff_im.mp h.symm
  apply Complex.ext
  · simp [Params.phiHatR]
  · simp [Params.phiHatR, him]





end GzGp



end Zeta23
end
open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23
open GzGp
variable (P : Params) (T : ℝ)

theorem solution (k l : Fin (P.d T)) :
    (∫ τ : ℝ, paperFT (P.fk T k) τ * conj (paperFT (P.fk T l) τ) *
      (nuX (Real.exp (P.L T)) τ : ℂ)) = P.Gp T k l := by
  unfold Params.Gp Params.Gentry Params.X
  rw [← integral_complex_ofReal]
  congr 1
  ext τ
  rw [paperFT_fk, paperFT_fk, ← Complex.ofReal_sub, ← Complex.ofReal_sub,
    phiHat_ofReal, phiHat_ofReal, Complex.conj_ofReal]
  push_cast
  ring
