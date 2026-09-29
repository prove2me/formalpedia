-- Prove2me | Definitions.Def_Speculative_AutoResearch_FisherSimplexCurvature
-- name    : Speculative_AutoResearch_FisherSimplexCurvature
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:29:01.905547+00:00
-- url     : https://prove2.me/theorems/5bf31839-b2ed-4a59-9883-41f6e8d3c1c1
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_FisherSimplexCurvature
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.FisherSimplexCurvature`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/FisherSimplexCurvature.lean by skeleton subtraction
import Mathlib

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

namespace TrinomialFisher

/-! ## 1. The model, its scores, and the Fisher metric -/

/-- The three point-masses of the trinomial model at parameter `(x, y)`. -/
def prob : Fin 3 → ℝ → ℝ → ℝ
  | 0, x, _ => x
  | 1, _, y => y
  | 2, x, y => 1 - x - y

/-- The score functions `s_i(a) = ∂_i log p_a` of the trinomial model, in closed form. -/
def score : Fin 2 → Fin 3 → ℝ → ℝ → ℝ
  | 0, 0, x, _ => 1 / x
  | 0, 1, _, _ => 0
  | 0, 2, x, y => -1 / (1 - x - y)
  | 1, 0, _, _ => 0
  | 1, 1, _, y => 1 / y
  | 1, 2, x, y => -1 / (1 - x - y)





/-- The Fisher information metric `g_ij = E[s_i s_j]`. -/
def fisherMetric (i j : Fin 2) (x y : ℝ) : ℝ :=
  ∑ a : Fin 3, prob a x y * (score i a x y * score j a x y)

/-- The Amari–Chentsov cubic tensor `C_ijk = E[s_i s_j s_k]`. -/
def amariC (i j k : Fin 2) (x y : ℝ) : ℝ :=
  ∑ a : Fin 3, prob a x y * (score i a x y * score j a x y * score k a x y)

/-- Closed form of the Fisher metric on the trinomial simplex. -/
def gL : Fin 2 → Fin 2 → ℝ → ℝ → ℝ
  | 0, 0, x, y => 1 / x + 1 / (1 - x - y)
  | 0, 1, x, y => 1 / (1 - x - y)
  | 1, 0, x, y => 1 / (1 - x - y)
  | 1, 1, x, y => 1 / y + 1 / (1 - x - y)



/-! ## 2. Partial derivatives of the metric, and the Amari–Chentsov tensor -/

/-- Closed form for `∂_k g_ij`. -/
def dgL : Fin 2 → Fin 2 → Fin 2 → ℝ → ℝ → ℝ
  | 0, 0, 0, x, y => -1 / x ^ 2 + 1 / (1 - x - y) ^ 2
  | 0, 0, 1, x, y => 1 / (1 - x - y) ^ 2
  | 0, 1, 0, x, y => 1 / (1 - x - y) ^ 2
  | 0, 1, 1, x, y => 1 / (1 - x - y) ^ 2
  | 1, 0, 0, x, y => 1 / (1 - x - y) ^ 2
  | 1, 0, 1, x, y => 1 / (1 - x - y) ^ 2
  | 1, 1, 0, x, y => 1 / (1 - x - y) ^ 2
  | 1, 1, 1, x, y => -1 / y ^ 2 + 1 / (1 - x - y) ^ 2










/-! ## 3. The Levi-Civita connection: Christoffel symbols of the first kind -/

/-- Christoffel symbols of the first kind, `Γ_{ij,l} = ½(∂_i g_jl + ∂_j g_il - ∂_l g_ij)`. -/
def chrLow (i j l : Fin 2) (x y : ℝ) : ℝ :=
  (dgL i j l x y + dgL j i l x y - dgL l i j x y) / 2







/-! ## 4. The inverse metric and the Christoffel symbols of the second kind -/

/-- The inverse Fisher metric: the multinomial covariance `g^{ij} = δ_ij p_i - p_i p_j`. -/
def gInv : Fin 2 → Fin 2 → ℝ → ℝ → ℝ
  | 0, 0, x, _ => x * (1 - x)
  | 0, 1, x, y => -(x * y)
  | 1, 0, x, y => -(x * y)
  | 1, 1, _, y => y * (1 - y)



/-- Christoffel symbols of the second kind `Γ^k_{ij}`, in closed form. -/
def chr : Fin 2 → Fin 2 → Fin 2 → ℝ → ℝ → ℝ
  | 0, 0, 0, x, y => (x / (1 - x - y) - 1 / x + 1) / 2
  | 1, 0, 0, x, y => (y / (1 - x - y) + y / x) / 2
  | 0, 0, 1, x, y => (x / (1 - x - y)) / 2
  | 0, 1, 0, x, y => (x / (1 - x - y)) / 2
  | 1, 0, 1, x, y => (y / (1 - x - y)) / 2
  | 1, 1, 0, x, y => (y / (1 - x - y)) / 2
  | 0, 1, 1, x, y => (x / (1 - x - y) + x / y) / 2
  | 1, 1, 1, x, y => (y / (1 - x - y) - 1 / y + 1) / 2



/-! ## 5. Partial derivatives of the Christoffel symbols -/

/-- Closed form for `∂_d Γ^k_{ij}`. -/
def dchr : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ → ℝ → ℝ
  | 0, 0, 0, 0, x, y => (1 / (1 - x - y) + x / (1 - x - y) ^ 2 + 1 / x ^ 2) / 2
  | 1, 0, 0, 0, x, y => (x / (1 - x - y) ^ 2) / 2
  | 0, 1, 0, 0, x, y => (y / (1 - x - y) ^ 2 - y / x ^ 2) / 2
  | 1, 1, 0, 0, x, y => (1 / (1 - x - y) + y / (1 - x - y) ^ 2 + 1 / x) / 2
  | 0, 0, 0, 1, x, y => (1 / (1 - x - y) + x / (1 - x - y) ^ 2) / 2
  | 1, 0, 0, 1, x, y => (x / (1 - x - y) ^ 2) / 2
  | 0, 0, 1, 0, x, y => (1 / (1 - x - y) + x / (1 - x - y) ^ 2) / 2
  | 1, 0, 1, 0, x, y => (x / (1 - x - y) ^ 2) / 2
  | 0, 1, 0, 1, x, y => (y / (1 - x - y) ^ 2) / 2
  | 1, 1, 0, 1, x, y => (1 / (1 - x - y) + y / (1 - x - y) ^ 2) / 2
  | 0, 1, 1, 0, x, y => (y / (1 - x - y) ^ 2) / 2
  | 1, 1, 1, 0, x, y => (1 / (1 - x - y) + y / (1 - x - y) ^ 2) / 2
  | 0, 0, 1, 1, x, y => (1 / (1 - x - y) + x / (1 - x - y) ^ 2 + 1 / y) / 2
  | 1, 0, 1, 1, x, y => (x / (1 - x - y) ^ 2 - x / y ^ 2) / 2
  | 0, 1, 1, 1, x, y => (y / (1 - x - y) ^ 2) / 2
  | 1, 1, 1, 1, x, y => (1 / (1 - x - y) + y / (1 - x - y) ^ 2 + 1 / y ^ 2) / 2



/-! ## 6. Curvature -/

/-- The Riemann tensor of an arbitrary affine connection on a `2`-dimensional chart:
`R^l_{k i j} = ∂_i Γ^l_{jk} - ∂_j Γ^l_{ik} + Γ^l_{im} Γ^m_{jk} - Γ^l_{jm} Γ^m_{ik}`. -/
def riemann (G : Fin 2 → Fin 2 → Fin 2 → ℝ) (dG : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
    (l k i j : Fin 2) : ℝ :=
  dG i l j k - dG j l i k + ∑ m : Fin 2, (G l i m * G m j k - G l j m * G m i k)

/-- The sectional (Gauss) curvature scalar `⟨R(∂₀,∂₁)∂₁, ∂₀⟩ / det g`. -/
def sectional (g : Fin 2 → Fin 2 → ℝ) (G : Fin 2 → Fin 2 → Fin 2 → ℝ)
    (dG : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ) : ℝ :=
  (∑ l : Fin 2, riemann G dG l 1 0 1 * g l 0) / (g 0 0 * g 1 1 - g 0 1 * g 1 0)

/-- The curvature scalar of Amari's `α`-connection on the trinomial simplex. -/
def alphaCurv (a x y : ℝ) : ℝ :=
  sectional (fun i j => gL i j x y) (fun k i j => (1 + a) * chr k i j x y)
    (fun d k i j => (1 + a) * dchr d k i j x y)

/-- The Gauss curvature of the Fisher–Rao metric on the trinomial simplex. -/
def gaussianCurvature (x y : ℝ) : ℝ := alphaCurv 0 x y






end TrinomialFisher


