-- Prove2me | Theorems.Thm_MultiHeadPlumbing_residual_injective_of_lipschitz
-- name    : MultiHeadPlumbing.residual_injective_of_lipschitz
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:30.460818+00:00
-- url     : https://prove2.me/theorems/b26b8d62-74e8-495c-be4c-86bffc4b537a
-- title:
--   Residual connections with a contractive block are injective: no information is lost.
-- statement:
--   Residual connections with a contractive block are injective: no information is lost.
--
--   ```lean
--   theorem MultiHeadPlumbing.residual_injective_of_lipschitz(f : E → E) (L : ℝ) (hL : L < 1)
--       (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
--       Function.Injective (residual f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean#L92

-- Thm stub generated from MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_MultiHeadPlumbing

/-!
# Dimension-safe multi-head plumbing: projections, concatenation, residuals, feed-forward

The catalog transformer file works with a single bilinear score and one head per input.  This
file adds the standard architectural plumbing with dimension-safe matrix types and proves the
structural facts that make it meaningful:

* `qkScore_eq_bilinear` — separate query/key projections are *exactly* the bilinear score of
  the catalog file, with matrix `WQᵀ * WK`;
* `rank_qk_le_headDim` and `qk_ne_one_of_headDim_lt` — the **low-rank bottleneck**: a head of
  width `dk` can only realize score matrices of rank at most `dk`, so for `dk < d` no head can
  implement the identity score pattern.  This is an architectural lower bound;
* `outputProj_concat` — the standard identity that an output projection applied to the
  concatenation of heads is the sum of per-head projections, i.e. multi-head attention is a
  sum of independent head contributions;
* `residual_injective_of_lipschitz` — residual connections with a contractive block are
  injective (information preserving);
* `ffn_pos_homogeneous` — an unbiased ReLU feed-forward block is positively homogeneous.
-/

open scoped BigOperators
open Matrix

open MultiHeadPlumbing


variable {d dk : ℕ}







variable {H dv d : ℕ}






variable {E : Type*} [NormedAddCommGroup E]

theorem MultiHeadPlumbing.residual_injective_of_lipschitz(f : E → E) (L : ℝ) (hL : L < 1)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Function.Injective (residual f) := by sorry
