-- Prove2me | Theorems.Thm_SplitCountLaw_mutualInfo_pos
-- name    : SplitCountLaw.mutualInfo_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:23.297879+00:00
-- url     : https://prove2.me/theorems/b6a953b4-4f01-4eb1-a710-f226843c4619
-- title:
--   Strict positivity.
-- statement:
--   **Strict positivity.** A normalised table with one cell off the independent
--   product carries strictly positive information.
--
--   ```lean
--   theorem SplitCountLaw.mutualInfo_pos(p : α → β → ℝ) (hp : ∀ a b, 0 ≤ p a b)
--       (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b)
--       (htot : ∑ a, rowMarg p a = 1) {a₀ : α} {b₀ : β}
--       (hne : p a₀ b₀ ≠ rowMarg p a₀ * colMarg p b₀) :
--       0 < mutualInfo p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitCountLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitCountLaw.lean#L405

-- Thm stub generated from Novelty/SplitCountLaw.lean
import Mathlib
import Definitions.Def_Novelty_SplitCountLaw

/-!
# Finite mutual information: log-sum, data processing, and the `I ≤ H(A)` cap

This file develops, from first principles, the small amount of information theory
needed by `Novelty.SplitCountChannel` (the SPLIT-COUNT-LAW experiment).

Everything is phrased for a *finite joint weight table* `p : α → β → ℝ` with
nonnegative entries; the mutual information is measured in **bits**:

`mutualInfo p = ∑ a ∑ b, p a b * logb 2 (p a b / (rowMarg p a * colMarg p b))`.

Main results.

* `Real.logsum_inequality` : the log-sum inequality
  `(∑ aᵢ) * log ((∑ aᵢ)/(∑ bᵢ)) ≤ ∑ aᵢ * log (aᵢ / bᵢ)` for `aᵢ ≥ 0`, `bᵢ > 0`.
* `mutualInfo_map_le` : the **data processing inequality** for a deterministic
  relabelling `g : β → γ` of the second coordinate.
* `mutualInfo_le_rowEntropy` : `I(A;B) ≤ H(A)`.
* `mutualInfo_le_one_of_binary` : for a binary first coordinate, `I(A;B) ≤ 1` bit.
* `mutualInfo_nonneg` : `I(A;B) ≥ 0`.

No probabilistic measure theory is used: all statements are elementary real
inequalities about finite tables, which is exactly the level at which the
split-count experiment lives.
-/

open SplitCountLaw

open Finset Real





/-! ## The log-sum inequality -/







/-! ## Data processing -/


variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]






/-! ## The `I ≤ H(A)` cap -/


variable {α β : Type*} [Fintype α] [Fintype β]







/-! ## Channel decomposition `I = H(B) - H(B|A)` -/


variable {α β : Type*} [Fintype α] [Fintype β]



/-! ## Nonnegativity -/


variable {α β : Type*} [Fintype α] [Fintype β]

theorem SplitCountLaw.mutualInfo_pos(p : α → β → ℝ) (hp : ∀ a b, 0 ≤ p a b)
    (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b)
    (htot : ∑ a, rowMarg p a = 1) {a₀ : α} {b₀ : β}
    (hne : p a₀ b₀ ≠ rowMarg p a₀ * colMarg p b₀) :
    0 < mutualInfo p := by sorry
