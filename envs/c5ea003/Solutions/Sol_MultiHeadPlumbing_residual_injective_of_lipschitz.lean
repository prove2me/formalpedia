-- Prove2me | solution 1 for MultiHeadPlumbing.residual_injective_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:13.649888+00:00
-- url     : https://prove2.me/submissions/00d3a47e-813c-46bd-9b24-05a77b842b56

-- Sol generated from MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean
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






variable {d dff : ℕ}







open MultiHeadPlumbing in
theorem solution(f : E → E) (L : ℝ) (hL : L < 1)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    Function.Injective (residual f) := by
  intro x y hxy
  have h : x + f x = y + f y := hxy
  have hkey : ‖x - y‖ ≤ L * ‖x - y‖ := by
    have hz : (x - y) + (f x - f y) = 0 := by
      have hab : (x - y) + (f x - f y) = (x + f x) - (y + f y) := by abel
      rw [hab, h, sub_self]
    have h2 : x - y = -(f x - f y) := eq_neg_of_add_eq_zero_left hz
    calc ‖x - y‖ = ‖f x - f y‖ := by rw [h2, norm_neg]
      _ ≤ L * ‖x - y‖ := hf x y
  have hnn : 0 ≤ ‖x - y‖ := norm_nonneg _
  have : ‖x - y‖ = 0 := by nlinarith
  have := norm_eq_zero.mp this
  exact sub_eq_zero.mp this
