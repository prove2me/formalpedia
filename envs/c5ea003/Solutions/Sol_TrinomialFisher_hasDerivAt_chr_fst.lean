-- Prove2me | solution 1 for TrinomialFisher.hasDerivAt_chr_fst
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:22:54.723098+00:00
-- url     : https://prove2.me/submissions/58dea50d-b56e-4622-9593-a985db4159b0

-- Sol generated from Speculative/AutoResearch/FisherSimplexCurvature.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_FisherSimplexCurvature

/-!
# The Levi-Civita connection and Gaussian curvature of a concrete finite-support model

This file carries out, **completely explicitly and with no `sorry`**, the full
Riemannian computation for the smallest genuinely two-dimensional finite-support
statistical model: the *open trinomial simplex*

  `Δ° = {(x, y) : x > 0, y > 0, 1 - x - y > 0}`,
  `p_(x,y) = (x, y, 1 - x - y)` on the three-point sample space `Fin 3`,

equipped with its Fisher–Rao metric.

The pipeline is deliberately staged so that **each geometric object is derived,
not postulated**:

1. `score`  — the score functions are *proved* to be the logarithmic derivatives
   of the model (`hasDerivAt_log_prob_fst/snd`).
2. `fisherMetric` — defined as `E[s_i s_j]` and *proved* equal to the closed form
   `gL` (`fisherMetric_eq_gL`).
3. `dgL` — *proved* to be the genuine partial derivatives of `gL`
   (`hasDerivAt_gL_fst/snd`).
4. `amariC` — the Amari–Chentsov cubic tensor `E[s_i s_j s_k]`; we prove the
   *mixture-coordinate* identity `∂_k g_ij = - C_ijk` (`dgL_eq_neg_amariC`).
5. `chrLow` — the Christoffel symbols of the first kind, together with a general
   Koszul-type **uniqueness theorem** (`levi_civita_unique`) showing that they are
   the *only* torsion-free metric-compatible candidate.
6. `gInv`, `chr` — the inverse metric and the Christoffel symbols of the second
   kind, in closed form, *proved* to be the raised `chrLow` (`chr_eq_raise`).
7. `dchr` — *proved* to be the partial derivatives of `chr`
   (`hasDerivAt_chr_fst/snd`).
8. `riemann`, `sectional`, `alphaCurv` — the curvature machinery, and the two
   headline results:

   * `gaussianCurvature_eq` : the Gauss curvature of the Fisher–Rao metric on the
     trinomial simplex is the **constant `+1/4`** — the model is a piece of a round
     sphere of radius `2`, *not* a hyperbolic plane;
   * `alphaCurv_eq` : for Amari's whole one-parameter family of `α`-connections the
     curvature scalar is `(1 - α²)/4`, which is `≥ 0` for `|α| ≤ 1` and vanishes
     exactly at the dually flat endpoints `α = ±1`.

The methodological point of the mission — *"test curvature only after
identifiability; constant negative curvature is a separate claim, not a corollary
of exponential sensitivity"* — is settled in the companion file
`Combinatorics.FisherSimplexCurvatureConsequences`.
-/

open Finset

noncomputable section

open TrinomialFisher

/-! ## 1. The model, its scores, and the Fisher metric -/












/-! ## 2. Partial derivatives of the metric, and the Amari–Chentsov tensor -/



/-- `t ↦ c / (1 - t - y)` differentiated at `x`. -/
theorem hasDerivAt_constDivZ_fst (c x y : ℝ) (hz : 1 - x - y ≠ 0) :
    HasDerivAt (fun t : ℝ => c / (1 - t - y)) (c / (1 - x - y) ^ 2) x := by
  have hlin : HasDerivAt (fun t : ℝ => 1 - t - y) (-1) x := by
    simpa using ((hasDerivAt_id x).const_sub (1 : ℝ)).sub_const y
  refine ((hasDerivAt_const x c).div hlin hz).congr_deriv ?_
  ring


/-- `t ↦ t / (1 - t - y)` differentiated at `x`. -/
theorem hasDerivAt_selfDivZ_fst (x y : ℝ) (hz : 1 - x - y ≠ 0) :
    HasDerivAt (fun t : ℝ => t / (1 - t - y)) (1 / (1 - x - y) + x / (1 - x - y) ^ 2) x := by
  have hlin : HasDerivAt (fun t : ℝ => 1 - t - y) (-1) x := by
    simpa using ((hasDerivAt_id x).const_sub (1 : ℝ)).sub_const y
  refine (((hasDerivAt_id x).div hlin hz)).congr_deriv ?_
  simp only [id_eq]
  field_simp
  ring


/-- `t ↦ c / t` differentiated at `x ≠ 0`. -/
theorem hasDerivAt_constDiv (c x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => c / t) (-c / x ^ 2) x := by
  refine ((hasDerivAt_const x c).div (hasDerivAt_id x) hx).congr_deriv ?_
  simp only [id_eq]
  field_simp
  ring




/-! ## 3. The Levi-Civita connection: Christoffel symbols of the first kind -/








/-! ## 4. The inverse metric and the Christoffel symbols of the second kind -/







/-! ## 5. Partial derivatives of the Christoffel symbols -/




/-! ## 6. Curvature -/











open TrinomialFisher in
theorem solution(k i j : Fin 2) (x y : ℝ)
    (hx : x ≠ 0) (hz : 1 - x - y ≠ 0) :
    HasDerivAt (fun t => chr k i j t y) (dchr 0 k i j x y) x := by
  have hA := hasDerivAt_selfDivZ_fst x y hz
  have hC := hasDerivAt_constDiv 1 x hx
  have hCy := hasDerivAt_constDiv y x hx
  have hBy := hasDerivAt_constDivZ_fst y x y hz
  have hDy : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).div_const y
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp only [chr, dchr]
  · refine (((hA.sub hC).add_const 1).div_const 2).congr_deriv ?_; ring
  · exact hA.div_const 2
  · exact hA.div_const 2
  · refine ((hA.add hDy).div_const 2).congr_deriv ?_; ring
  · refine ((hBy.add hCy).div_const 2).congr_deriv ?_; ring
  · exact hBy.div_const 2
  · exact hBy.div_const 2
  · refine (((hBy.sub_const (1 / y)).add_const 1).div_const 2).congr_deriv ?_; ring
