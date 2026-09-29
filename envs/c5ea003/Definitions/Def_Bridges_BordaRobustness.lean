-- Prove2me | Definitions.Def_Bridges_BordaRobustness
-- name    : Bridges_BordaRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:22.836262+00:00
-- url     : https://prove2.me/theorems/bede31cf-c3ce-4451-a550-dd17d5bcf91c
-- title:
--   Aether Catalog definitions — Bridges_BordaRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BordaRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BordaRobustness.lean by skeleton subtraction
import Mathlib
/-
# GL3 Tropical Satake Certified Robustness for Borda-Count Hecke Score Aggregation

This module develops a formal robustness theory for multiclass classifiers whose
final prediction is obtained by Borda aggregation of pairwise score comparisons.

We work over a finite label type `α` with `[Fintype α] [DecidableEq α]`, proving:

1. **Pairwise margin perturbation bounds**: Each pairwise margin `S_i - S_j` changes
   by at most `2η` when individual scores change by at most `η`.

2. **Weighted Borda perturbation bounds**: The weighted Borda surrogate
   `Ω_i(S) = Σ_{j≠i} (S_i - S_j)` satisfies a Lipschitz bound with constant `2(n-1)`.

3. **Weighted Borda winner certification**: If the margin between the winner's weighted
   Borda score and every other candidate exceeds `4(n-1)η`, the winner is preserved.

4. **Pairwise sign stability**: Sufficiently large pairwise margins cannot flip sign.

5. **Thresholded Borda invariance**: Under uniform pairwise separation `2η < |S_i - S_j|`,
   the discrete Borda score `B_i = Σ_{j≠i} 1[S_i > S_j]` is preserved exactly.

6. **Borda winner certification**: Combining the above yields a certified robustness
   theorem for the Borda winner.

7. **Structural lemmas**: The weighted Borda score satisfies `Ω_i = n·S_i - Σ_k S_k`
   and `Ω_i - Ω_j = n·(S_i - S_j)`.
-/

open Finset

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## Core definitions -/

/-- The pairwise margin between classes `i` and `j` under score vector `S`. -/
def pairMargin (S : α → ℝ) (i j : α) : ℝ :=
  S i - S j

/-- The weighted Borda score (Copeland-margin surrogate) for class `i`:
    `Ω_i(S) = Σ_{j ≠ i} (S_i - S_j)`. -/
def weightedBorda (S : α → ℝ) (i : α) : ℝ :=
  ∑ j ∈ (univ.erase i), pairMargin S i j

/-- The thresholded Borda score for class `i`:
    `B_i(S) = Σ_{j ≠ i} 1[S_i > S_j]`. -/
def bordaScore (S : α → ℝ) (i : α) : ℕ :=
  ∑ j ∈ (univ.erase i), if 0 < pairMargin S i j then 1 else 0


/-- Class `w` is a strict weighted Borda winner. -/
def strictWinnerWeighted (S : α → ℝ) (w : α) : Prop :=
  ∀ j, j ≠ w → weightedBorda S j < weightedBorda S w


/-- Class `w` is a strict Borda winner. -/
def strictWinnerBorda (S : α → ℝ) (w : α) : Prop :=
  ∀ j, j ≠ w → bordaScore S j < bordaScore S w

/-! ## Primary Theorem 1: Pairwise margin perturbation bound -/

/-
Each pairwise margin changes by at most `2η` when individual scores change by at most `η`.
    This is the fundamental perturbation lemma from which all other bounds follow.
-/

/-! ## Primary Theorem 1b: Weighted Borda perturbation bound -/

/-
The weighted Borda score changes by at most `2(n-1)η` when individual scores
    change by at most `η`. This is obtained by summing the pairwise margin bound.
-/

/-! ## Primary Theorem 2: Weighted Borda winner certification -/

/-
If the weighted Borda margin exceeds `4(n-1)η`, the strict winner is preserved
    under any perturbation bounded by `η`. The factor 4 accounts for both the winner's
    score decreasing and the challenger's score increasing.
-/

/-! ## Primary Theorem 3: Pairwise sign stability -/

/-
If the pairwise margin `S_i - S_j` exceeds `2η`, then it remains positive
    under any perturbation bounded by `η`.
-/

/-
Dual: if the pairwise margin is sufficiently negative, it remains negative.
-/

/-
The sign of a pairwise margin is preserved when `2η < |margin|`.
-/

/-! ## Primary Theorem 4: Thresholded Borda score invariance -/

/-
If every pairwise contest involving `i` has margin exceeding `2η`, then
    none of the indicator terms in `bordaScore` changes under perturbation.
-/

/-
Global version: if all pairwise margins exceed `2η`, all Borda scores are preserved.
-/

/-! ## Primary Theorem 5: Borda winner certification -/

/-
**Main Borda Robustness Theorem**: If `w` is a strict Borda winner under score vector `S`,
    and all pairwise margins exceed `2η`, then `w` remains a strict Borda winner under any
    perturbation bounded by `η`. This is the discrete analogue of the weighted Borda
    certification theorem.
-/

/-! ## Structural lemmas -/

/-
The weighted Borda score satisfies `Ω_i = n·S_i - Σ_k S_k`.
    This shows weighted Borda is an affine transform of the original class score.
-/

/-
The difference of weighted Borda scores satisfies `Ω_i - Ω_j = n·(S_i - S_j)`.
    This shows the weighted Borda winner agrees with the argmax of `S`.
-/

/-
Specialization to `|α| = 3`: the weighted Borda perturbation constant is 4.
-/

/-! ## GL3 Specialization -/

/-
GL3 certified radius form: if the GL3 tropical Satake score perturbation satisfies
    `|S_c(x+δ) - S_c(x)| ≤ K·ε`, then the weighted Borda winner is preserved when
    the margin exceeds `4(n-1)·K·ε`.
-/

/-
GL3 certified radius form for thresholded Borda: the Borda winner is preserved
    when all pairwise margins exceed `2·K·ε`.
-/

end


