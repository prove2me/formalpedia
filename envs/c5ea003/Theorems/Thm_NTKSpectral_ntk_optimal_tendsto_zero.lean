-- Prove2me | Theorems.Thm_NTKSpectral_ntk_optimal_tendsto_zero
-- name    : NTKSpectral.ntk_optimal_tendsto_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:43.173923+00:00
-- url     : https://prove2.me/theorems/e4dd8443-4601-4317-a368-6c1ee624da5e
-- title:
--   NTK spectral convergence theorem.
-- statement:
--   **NTK spectral convergence theorem.** Suppose the NTK has a strictly positive
--   spectrum `0 < λ_min ≤ λ ≤ λ_max` and we train with the optimal learning rate
--   `η* = 2/(λ_min+λ_max)`. Then any residual mode `c` evolving by
--   `c_{k+1} = (1 - η* λ) c_k` converges to `0`. This packages the spectral picture:
--   *positive definiteness of the NTK ⇒ global convergence of lazy training.*
--
--   ```lean
--   theorem NTKSpectral.ntk_optimal_tendsto_zero(lmin lmax lam : ℝ)
--       (hmin : 0 < lmin) (h1 : lmin ≤ lam) (h2 : lam ≤ lmax)
--       (c : ℕ → ℝ)
--       (hrec : ∀ k, c (k + 1) = (1 - (2 / (lmin + lmax)) * lam) * c k) :
--       Tendsto c atTop (nhds 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PosetTheory/NTKSpectral.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PosetTheory/NTKSpectral.lean#L173

-- Thm stub generated from MachineLearning/PosetTheory/NTKSpectral.lean
import Mathlib
import Definitions.Def_MachineLearning_PosetTheory_NTKSpectral
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# NTK Spectral Convergence

This file develops, from a cold start, the spectral theory of the **Neural Tangent
Kernel (NTK)** that governs the convergence of gradient-based training in the
infinite-width / linearized regime.

The NTK of a model with feature/Jacobian matrix `J` is the Gram matrix
`Θ = Jᵀ J`. In the lazy-training regime, the training residual `r` evolves under
gradient descent as `r_{k+1} = (I - η Θ) r_k`. Decomposing the residual in the
eigenbasis of `Θ` turns this matrix recurrence into independent scalar modes
`c_{k+1} = (1 - η λ) c_k`, one per eigenvalue `λ`. Hence the *entire* convergence
behaviour of training is controlled by the **spectrum** of `Θ`.

## Main results

* `ntkGram_posSemidef` — the NTK Gram matrix `Jᵀ J` is positive semidefinite.
* `ntk_quadratic_form` — the NTK quadratic form equals the squared feature-space
  norm: `xᵀ (Jᵀ J) x = ‖J x‖²`.
* `ntk_quadratic_form_nonneg` — consequently the NTK quadratic form is `≥ 0`.
* `ntk_mode_decay` — closed form of a single spectral mode: `c k = (1 - η λ)ᵏ c₀`.
* `optimal_lr_contraction` — with the optimal learning rate `η* = 2/(λ_min+λ_max)`,
  every mode contracts by the condition-number factor
  `(λ_max - λ_min)/(λ_max + λ_min) = (κ-1)/(κ+1)`.
* `geometric_convergence` — a per-step contraction by `ρ` yields `|c k| ≤ ρᵏ |c₀|`.
* `contraction_tendsto_zero` — if `ρ < 1` the residual converges to `0`.
* `ntk_optimal_tendsto_zero` — capstone: a positive-definite NTK spectrum
  (`0 < λ_min ≤ λ_max`) trained at the optimal rate drives every mode to `0`.

## References

The neural tangent kernel was introduced by Jacot, Gabriel and Hongler (2018);
the link between the smallest NTK eigenvalue and the gradient-descent convergence
rate is standard in the lazy-training literature. The condition-number contraction
`(κ-1)/(κ+1)` is the classical optimal rate for gradient descent on quadratics.
-/

open NTKSpectral

open Matrix Filter

-- !-- Lab Notebook -- !--
-- Hypothesis: The convergence of gradient descent in the NTK (lazy) regime is
--   entirely governed by the spectrum of the Gram matrix Θ = Jᵀ J: positive
--   semidefiniteness guarantees non-amplifying modes, and the condition number
--   κ = λ_max/λ_min controls the optimal contraction rate.
-- Result: Formalized the full chain — (1) Θ is PSD with quadratic form equal to
--   the squared feature norm; (2) each eigen-mode follows c_{k+1}=(1-ηλ)c_k with
--   closed form (1-ηλ)ᵏc₀; (3) at η*=2/(λmin+λmax) every mode contracts by
--   (λmax-λmin)/(λmax+λmin); (4) this yields geometric convergence to 0.
-- Insight: The spectral diagonalization turns the matrix recurrence into scalar
--   modes, so the global convergence theorem reduces to a one-dimensional
--   contraction lemma plus a clean condition-number inequality. The PSD result
--   and the contraction result are genuinely cross-domain: linear algebra meets
--   optimization dynamics.
-- Failure analysis: A direct ODE / matrix-exponential treatment of the
--   continuous-time flow ṙ = -Θ r was abandoned — Mathlib's ODE API makes the
--   matrix-exponential energy estimate heavy. The discrete spectral-mode route
--   captures the same mathematics (rate = condition number) with clean, fully
--   verified proofs, and is closer to what actual optimizers run.

/-! ## Section 1: The NTK Gram matrix and its spectrum -/


-- !-- The NTK Gram matrix is `Aᴴ A` with `A = J`; over ℝ conjugate-transpose is
--     transpose, so `Matrix.posSemidef_conjTranspose_mul_self` applies directly. -- !--

-- !-- Expand `(Jᵀ J) *ᵥ x = Jᵀ *ᵥ (J *ᵥ x)`, push the `x` through `dotProduct_mulVec`
--     and `vecMul_transpose` to land on `(J x) ⬝ᵥ (J x)`. -- !--


/-! ## Section 2: Spectral modes of gradient descent -/

-- !-- Induction on `k`: the base case is `h0`, and the step rewrites with the
--     recurrence and `pow_succ`. -- !--

-- !-- Write `1 - η λ` over the common denominator `λmin+λmax`; the bound reduces
--     to `|λmin+λmax-2λ| ≤ λmax-λmin`, which is exactly `λmin ≤ λ ≤ λmax`. -- !--

/-! ## Section 3: From contraction to convergence -/

-- !-- Induction on `k`: combine the one-step bound `|s (k+1)| ≤ ρ |s k|` with the
--     inductive `|s k| ≤ ρᵏ |s 0|`, using `ρ ≥ 0` for monotonicity. -- !--

-- !-- Squeeze `|s k|` between `0` and `ρᵏ |s 0| → 0` (using `ρ < 1`), then conclude
--     `s k → 0` via the norm-squeeze lemma. -- !--

/-! ## Section 4: Capstone — spectrum controls convergence -/

-- !-- Assemble: `optimal_lr_contraction` shows each mode contracts by
--     `ρ = (λmax-λmin)/(λmax+λmin) < 1`; feed that into `contraction_tendsto_zero`. -- !--

theorem NTKSpectral.ntk_optimal_tendsto_zero(lmin lmax lam : ℝ)
    (hmin : 0 < lmin) (h1 : lmin ≤ lam) (h2 : lam ≤ lmax)
    (c : ℕ → ℝ)
    (hrec : ∀ k, c (k + 1) = (1 - (2 / (lmin + lmax)) * lam) * c k) :
    Tendsto c atTop (nhds 0) := by sorry
