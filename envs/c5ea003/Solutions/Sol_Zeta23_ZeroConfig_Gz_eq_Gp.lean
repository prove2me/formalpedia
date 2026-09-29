-- Prove2me | solution 1 for Zeta23.ZeroConfig.Gz_eq_Gp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:11:44.439101+00:00
-- url     : https://prove2.me/submissions/339a94b4-ecf2-42a1-9572-21373d839a6e

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
import Theorems.Thm_Zeta23_GzGp_EFrhs_eq_Gp
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



/-- f_k ∈ C² given φ ∈ C² (as a ℂ-valued function). -/
lemma fk_contDiff (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ))) (k : ℤ) :
    ContDiff ℝ 2 (P.fk T k) := by
  unfold Params.fk
  apply hφC2.mul
  apply Complex.contDiff_exp.comp
  apply ContDiff.neg
  apply ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff

/-- supp f_k ⊆ supp φ ⊆ [−L/2, L/2]. -/
lemma fk_tsupport (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) (k : ℤ) :
    tsupport (P.fk T k) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) := by
  refine (tsupport_mul_subset_left).trans (subset_trans (le_of_eq ?_) hφsupp)
  show tsupport (Complex.ofReal ∘ P.phi T) = tsupport (P.phi T)
  simp only [tsupport, Function.support_comp_eq Complex.ofReal (by simp) (P.phi T)]

/-- Zero side: G_{kl} [eq:Gdef, 1st expr] is literally W(f_k, f_l) [eq:Wdef]. No hypotheses. -/
lemma Gz_eq_W (Z : ZeroConfig) (k l : Fin (P.d T)) :
    Z.Gz P T k l = Z.W (P.fk T k) (P.fk T l) := by
  unfold ZeroConfig.Gz ZeroConfig.W ZeroConfig.Gsummand ZeroConfig.Wsummand
  congr 1
  ext ρ
  rw [paperFT_fk, paperFT_fk, ← Complex.conj_ofReal (P.tau T l), ← map_sub,
    phiHat_conj, Complex.conj_conj, Complex.conj_ofReal]


end GzGp



end Zeta23
end
open scoped ComplexConjugate
open Complex MeasureTheory Set
open Zeta23

theorem solution (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hEF : ExplicitFormulaPaper Z) (hL : 0 < P.L T)
    (hφC2 : ContDiff ℝ 2 (fun u => (P.phi T u : ℂ)))
    (hφsupp : tsupport (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2)) :
    Z.Gz P T = P.Gp T := by
  ext k l
  obtain ⟨-, -, hW⟩ := hEF (P.L T) hL (P.fk T k) (P.fk T l) (GzGp.fk_contDiff P T hφC2 k)
    (GzGp.fk_contDiff P T hφC2 l) (GzGp.fk_tsupport P T hφsupp k) (GzGp.fk_tsupport P T hφsupp l)
  rw [GzGp.Gz_eq_W, hW, GzGp.EFrhs_eq_Gp]
