-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_MultiHeadPlumbing
-- name    : MachineLearning_TransformerUniversality_MultiHeadPlumbing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:34.942967+00:00
-- url     : https://prove2.me/theorems/ed47bb66-d88b-42cb-ba08-4bdbc3f6075f
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_MultiHeadPlumbing
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.MultiHeadPlumbing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/MultiHeadPlumbing.lean by skeleton subtraction
import Mathlib

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

namespace MultiHeadPlumbing

section Projections

variable {d dk : ℕ}

/-- Scaled dot-product score computed through explicit query and key projections. -/
def qkScore (WQ WK : Matrix (Fin dk) (Fin d) ℝ) (q k : Fin d → ℝ) : ℝ :=
  (WQ *ᵥ q) ⬝ᵥ (WK *ᵥ k)




end Projections

section Concatenation

variable {H dv d : ℕ}

/-- Concatenate the outputs of `H` heads, each of width `dv`, into one vector. -/
def concatHeads (v : Fin H → Fin dv → ℝ) : Fin H × Fin dv → ℝ := fun p => v p.1 p.2

/-- The block of the output projection acting on head `h`. -/
def outputBlock (WO : Matrix (Fin d) (Fin H × Fin dv) ℝ) (h : Fin H) :
    Matrix (Fin d) (Fin dv) ℝ := fun i b => WO i (h, b)


end Concatenation

section Residual

variable {E : Type*} [NormedAddCommGroup E]

/-- A residual block. -/
def residual (f : E → E) (x : E) : E := x + f x



end Residual

section FeedForward

variable {d dff : ℕ}

/-- Rectified linear unit. -/
def relu (t : ℝ) : ℝ := max t 0

/-- An unbiased two-layer ReLU feed-forward block. -/
def ffn (W₁ : Matrix (Fin dff) (Fin d) ℝ) (W₂ : Matrix (Fin d) (Fin dff) ℝ)
    (x : Fin d → ℝ) : Fin d → ℝ :=
  W₂ *ᵥ (fun j => relu ((W₁ *ᵥ x) j))



end FeedForward

end MultiHeadPlumbing


