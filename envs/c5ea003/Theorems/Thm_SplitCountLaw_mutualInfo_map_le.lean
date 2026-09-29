-- Prove2me | Theorems.Thm_SplitCountLaw_mutualInfo_map_le
-- name    : SplitCountLaw.mutualInfo_map_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:10.88548+00:00
-- url     : https://prove2.me/theorems/d360d7d3-fec4-4a9e-af44-c4c9f7b15c10
-- title:
--   Data processing inequality.
-- statement:
--   **Data processing inequality.**  Relabelling the second coordinate by a
--   deterministic map cannot increase the mutual information.
--
--   ```lean
--   theorem SplitCountLaw.mutualInfo_map_le(p : α → β → ℝ) (g : β → γ)
--       (hp : ∀ a b, 0 ≤ p a b) (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b) :
--       mutualInfo (push p g) ≤ mutualInfo p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitCountLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitCountLaw.lean#L215

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

theorem SplitCountLaw.mutualInfo_map_le(p : α → β → ℝ) (g : β → γ)
    (hp : ∀ a b, 0 ≤ p a b) (hrow : ∀ a, 0 < rowMarg p a) (hcol : ∀ b, 0 < colMarg p b) :
    mutualInfo (push p g) ≤ mutualInfo p := by sorry
