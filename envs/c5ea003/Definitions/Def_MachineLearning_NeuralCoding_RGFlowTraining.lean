-- Prove2me | Definitions.Def_MachineLearning_NeuralCoding_RGFlowTraining
-- name    : MachineLearning_NeuralCoding_RGFlowTraining
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:41.379809+00:00
-- url     : https://prove2.me/theorems/09abbc4e-4453-4db2-86c9-1e54bc143674
-- title:
--   Aether Catalog definitions — MachineLearning_NeuralCoding_RGFlowTraining
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NeuralCoding.RGFlowTraining`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NeuralCoding/RGFlowTraining.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- This file develops the RG-flow viewpoint on top of the spectral picture in
-- `MachineLearning/NTKSpectral.lean`; the relevant results there
-- (`ntkGram`, `ntk_mode_decay`, `ntk_optimal_tendsto_zero`) are referenced in the
-- docstrings. The development below is self-contained (`import Mathlib` only).

/-!
# Neural Network Training as Renormalization-Group Flow

This file formalizes the **renormalization-group (RG) picture of gradient-based
training** in the linearized / Neural-Tangent-Kernel (NTK) regime, building
directly on `Catalog/MachineLearning/NTKSpectral.lean`.

## The physical picture

In the NTK regime the training residual `r` evolves by `r_{k+1} = (I - η Θ) r_k`
with `Θ = JᵀJ` the NTK Gram matrix (cf. `NTKSpectral.ntkGram`). Diagonalizing `Θ`
turns the matrix recurrence into independent scalar modes, each rescaled by its
**gain** `g_i = 1 - η λ_i` (cf. `NTKSpectral.ntk_mode_decay`).

A single training step is therefore a *diagonal flow* `rgStep` on mode space that
rescales mode `i` by `g_i`. This is precisely a **renormalization-group step**:

* iterating the step is a discrete RG semigroup (`rgStep_semigroup`);
* modes with large NTK eigenvalue have small gain and decay fastest — these are
  the **high-frequency / irrelevant** directions that training "integrates out"
  (`rg_scale_separation`);
* the surviving **relevant** directions are the slow modes, and the RG flow runs
  to an **IR fixed point** which is exactly the kernel of the NTK
  (`rgStep_fixed_iff`);
* when every mode is contracting, the flow converges to that fixed point
  (`rg_flow_tendsto_zero`), a multi-mode generalization of
  `NTKSpectral.ntk_optimal_tendsto_zero`.

## Main results

* `rgStep_iterate` — closed form of the diagonal RG flow: `(rgStep)^[k] v i = g_i^k v_i`.
* `rgStep_semigroup` — the RG/training steps form a discrete one-parameter
  semigroup: coarse-graining to scale `k+m` = scale `m` then scale `k`.
* `rg_scale_separation` — **separation of scales**: a faster-contracting
  (higher-frequency) mode becomes negligible relative to a slower one; its
  amplitude ratio tends to `0`. This is the RG act of *integrating out* fast modes.
* `rgStep_fixed_iff` — the **IR fixed points** of the training flow are exactly the
  residuals annihilated by every active NTK eigenvalue (the NTK kernel).
* `rg_flow_tendsto_zero` — if every gain has `|g_i| < 1` the whole flow converges to
  the IR fixed point `0`.

## References

* Jacot, Gabriel, Hongler, *Neural Tangent Kernel* (2018).
* The RG interpretation of coarse-graining/optimization dynamics is folklore in the
  physics-of-learning literature; here it is given a fully verified algebraic core.
-/

open Filter
open scoped BigOperators

namespace RGFlowTraining

-- !-- Lab Notebook -- !--
-- Hypothesis: NTK-regime gradient descent is a renormalization-group flow on the
--   space of spectral modes. Each step rescales mode i by its gain g_i = 1-ηλ_i;
--   high NTK-eigenvalue modes contract fastest and are "integrated out", leaving a
--   relevant low-eigenvalue subspace whose IR fixed point is the NTK kernel.
-- Result: Formalized the diagonal RG step `rgStep`, its closed-form iterate
--   (g_i^k v_i), the semigroup law, scale separation (fast modes vanish relative
--   to slow ones), the fixed-point = NTK-kernel characterization, and global
--   convergence to the IR fixed point when all gains contract.
-- Insight: The "integrating out high-frequency modes" slogan becomes the precise
--   statement that the *ratio* of a fast mode to a slow mode tends to 0 — a
--   geometric-sequence fact once the iterate is in closed form. The RG semigroup
--   is exactly `Function.iterate_add`, and the IR fixed point is exactly the
--   kernel of the NTK, linking optimization dynamics to linear algebra.
-- Failure analysis: A continuous-time RG-flow ODE formulation was avoided (heavy
--   matrix-exponential API). The discrete diagonal flow captures the same scaling
--   physics with clean, fully verified proofs and reuses NTKSpectral directly.

/-- The per-mode **gain** of one training step: mode `i` with NTK eigenvalue `lam`
is rescaled by `1 - lr * lam` (cf. `NTKSpectral.ntk_mode_decay`). -/
def gain (lr lam : ℝ) : ℝ := 1 - lr * lam

/-- One **renormalization-group / training step**, modeled as the diagonal flow on
mode space that rescales each spectral mode `i` by its gain `1 - lr*(lam i)`. -/
def rgStep {d : ℕ} (lr : ℝ) (lam : Fin d → ℝ) (v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => gain lr (lam i) * v i

-- !-- Induction on `k`: `iterate_succ_apply'` peels one step, then `pow_succ`. -- !--

-- !-- `Function.iterate_add_apply` splits the iterate of a sum of scales. -- !--

-- !-- Read off coordinatewise: the IR fixed condition `(1-lr·lam_i)v_i = v_i`
--     simplifies to `lr·(lam_i·v_i)=0`, and `lr ≠ 0` cancels. -- !--

-- !-- `rgStep_iterate` writes the ratio as `(|g_i|/|g_j|)^k · (|v_i|/|v_j|)`;
--     the base is `< 1`, so the geometric sequence times a constant tends to `0`. -- !--

-- !-- Componentwise via `tendsto_pi_nhds`: each mode is `g_i^k v_i` with
--     `|g_i| < 1`, so `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` gives `→ 0`. -- !--

end RGFlowTraining


