-- Prove2me | Theorems.Thm_EMLLyapunovNL_lipschitzWith_one_of_monotone_homogeneous
-- name    : EMLLyapunovNL.lipschitzWith_one_of_monotone_homogeneous
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:34:40.197976+00:00
-- url     : https://prove2.me/theorems/bbc2d08f-7069-48ec-9c5f-4b97e920088e
-- title:
--   Crandall–Tartar for EML cells.
-- statement:
--   **Crandall–Tartar for EML cells.**  A monotone, translation-homogeneous cell is
--   automatically non-expansive in the sup norm — no weight constraint whatsoever is needed.
--
--   ```lean
--   theorem EMLLyapunovNL.lipschitzWith_one_of_monotone_homogeneous{f : (m → ℝ) → (m → ℝ)}
--       (hmono : Monotone f) (hhom : TranslationHomogeneous f) : LipschitzWith 1 f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EMLLyapunovTropical.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EMLLyapunovTropical.lean#L215

-- Thm stub generated from Novelty/EMLLyapunovTropical.lean
import Mathlib
import Definitions.Def_Novelty_EMLLyapunovTropical

/-!
# Lyapunov Exponents for Recurrent EML Architectures II: nonlinear and tropical cells

The linear theory (companion file `EMLLyapunovStability.lean`) measures gradient growth by
the norm of a Jacobian product.  For a *nonlinear* recurrent cell the right global object
is the **optimal Lipschitz constant** of the `T`-fold iterate,

`optLip f^[T] = inf {K ≥ 0 | ∀ x y, dist (f^[T] x) (f^[T] y) ≤ K * dist x y}`,

whose logarithmic growth rate is the (global, sup-norm) maximum Lyapunov exponent.  This
file proves two things.

1. **Saturated-activation cells.**  For `f = σ ∘ (W · + b)` with a `1`-Lipschitz
   activation `σ` (`tanh`, `ReLU`, hard-sigmoid, …) all iterates are `‖W‖ ^ T`-Lipschitz,
   the exponent is at most `log ‖W‖`, and the derivative of the unrolled network obeys
   `‖D(f^[T])‖ ≤ ‖W‖ ^ T` — a genuine non-exploding-gradient guarantee at the level of
   backpropagation, not merely of trajectories.

2. **A universal edge-of-chaos theorem.**  Any cell that is *monotone* and *translation
   homogeneous* is automatically non-expansive in the sup norm (a Crandall–Tartar type
   argument), and its Lipschitz constant is *exactly* `1` because uniform shifts are
   transported exactly.  Hence its maximum Lyapunov exponent is **exactly `0`**, with no
   hypothesis on the weights at all.  Two families of EML primitives are covered:

   * max-plus (tropical) cells `x ↦ (⨆ j, A i j + x j)_i`, the tropical analogue of a
     linear RNN — a bridge between tropical algebra and dynamical stability;
   * row-stochastic mixing cells `x ↦ (∑ j, P i j x j)_i`, the linear part of attention,
     averaging and consensus layers.

## Main results

* `optLip_le`, `le_optLip`, `optLip_eq_one` — calculus of the optimal Lipschitz constant.
* `lipschitzWith_emlCell`, `lipschitzWith_emlCell_iterate` — contraction budget of a
  saturated-activation recurrent cell.
* `norm_fderiv_emlCell_iterate_le` — the backpropagated derivative bound.
* `nlFtle_emlCell_le` — Lyapunov exponent bound `≤ log ‖W‖`.
* `exists_fixedPoint_emlCell` — a strict budget yields a unique stable memory state.
* `lipschitzWith_one_of_monotone_homogeneous`, `optLip_iterate_eq_one`,
  `nlMle_eq_zero_of_monotone_homogeneous` — the universal edge-of-chaos theorem.
* `lipschitzWith_one_tropCell`, `optLip_tropCell_iterate_eq_one`, `nlFtle_tropCell`,
  `nlMle_tropCell` — the tropical cell has maximum Lyapunov exponent exactly `0`.
* `nlMle_stochCell` — row-stochastic attention/averaging cells have exponent exactly `0`.
* `nlMle_dilationCell` — sharpness: translation homogeneity cannot be dropped.
* `nlMle_resCell_le`, `dist_resCell_iterate_le_exp`, `norm_fderiv_resCell_iterate_le_exp`,
  `nlMle_resCell_dilation` — residual (skip-connection) cells: the exact budget
  `log (1 + ‖W‖)`, and a *depth-uniform* gradient bound `exp c` under the critical
  depth scaling `‖W‖ ≤ c / T`.
* `GradedHomogeneous`, `nlMle_eq_log_of_monotone_graded` — the graded exponent theorem: a
  monotone cell answering a uniform shift `c` by `s · c` has exponent *exactly* `log s`.
* `nlMle_skip_eq_log_two`, `nlMle_averaged_skip` — a skip connection on any monotone
  homogeneous branch has exponent exactly `log 2`, and halving the sum restores `0`.
-/

open Filter Topology

open EMLLyapunovNL

/-! ## 1.  The optimal Lipschitz constant and the nonlinear Lyapunov exponent -/



variable {α : Type*} [PseudoMetricSpace α]









/-! ## 2.  Saturated-activation recurrent cells -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]









/-! ## 3.  A universal edge-of-chaos theorem for monotone, translation-homogeneous cells

Many recurrent EML primitives share two structural features: they are **monotone** (larger
inputs give larger outputs) and **translation homogeneous** (a uniform shift of the state
shifts the output by the same amount).  Max-plus (tropical) layers, min-plus layers,
maxout units, and row-stochastic attention/averaging layers are all of this type.  We prove
once and for all that any such cell has maximum Lyapunov exponent **exactly zero**.
-/


variable {m : Type*} [Fintype m] [Nonempty m]



omit [Nonempty m] in

theorem EMLLyapunovNL.lipschitzWith_one_of_monotone_homogeneous{f : (m → ℝ) → (m → ℝ)}
    (hmono : Monotone f) (hhom : TranslationHomogeneous f) : LipschitzWith 1 f := by sorry
