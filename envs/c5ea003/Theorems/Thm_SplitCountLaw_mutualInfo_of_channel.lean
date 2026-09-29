-- Prove2me | Theorems.Thm_SplitCountLaw_mutualInfo_of_channel
-- name    : SplitCountLaw.mutualInfo_of_channel
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:36:27.304037+00:00
-- url     : https://prove2.me/theorems/8c680e77-1769-4ed2-83f8-e160c564ccd0
-- title:
--   For a joint table built from a prior `w` and a channel `k` (`p a b = w a * k a b`),
-- statement:
--   For a joint table built from a prior `w` and a channel `k` (`p a b = w a * k a b`),
--   the mutual information is the output entropy minus the average conditional entropy.
--
--   ```lean
--   theorem SplitCountLaw.mutualInfo_of_channel(w : α → ℝ) (k : α → β → ℝ)
--       (hw : ∀ a, 0 ≤ w a) (hk : ∀ a b, 0 ≤ k a b) (hk1 : ∀ a, ∑ b, k a b = 1)
--       (hcol : ∀ b, 0 < colMarg (fun a b => w a * k a b) b) :
--       mutualInfo (fun a b => w a * k a b)
--         = entropyBits (colMarg (fun a b => w a * k a b)) - ∑ a, w a * entropyBits (k a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitCountLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitCountLaw.lean#L323

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

theorem SplitCountLaw.mutualInfo_of_channel(w : α → ℝ) (k : α → β → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hk : ∀ a b, 0 ≤ k a b) (hk1 : ∀ a, ∑ b, k a b = 1)
    (hcol : ∀ b, 0 < colMarg (fun a b => w a * k a b) b) :
    mutualInfo (fun a b => w a * k a b)
      = entropyBits (colMarg (fun a b => w a * k a b)) - ∑ a, w a * entropyBits (k a) := by sorry
