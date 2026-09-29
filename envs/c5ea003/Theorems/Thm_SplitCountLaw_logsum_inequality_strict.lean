-- Prove2me | Theorems.Thm_SplitCountLaw_logsum_inequality_strict
-- name    : SplitCountLaw.logsum_inequality_strict
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:35:39.662333+00:00
-- url     : https://prove2.me/theorems/5cb4df0e-fe95-4912-869b-ada992e9d91a
-- title:
--   Strict log-sum inequality: strict as soon as one ratio is off.
-- statement:
--   **Strict log-sum inequality**: strict as soon as one ratio is off.
--
--   ```lean
--   theorem SplitCountLaw.logsum_inequality_strict{ι : Type*} (s : Finset ι) (a b : ι → ℝ)
--       (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) {i₀ : ι} (hi₀ : i₀ ∈ s)
--       (hne : a i₀ * (∑ i ∈ s, b i) ≠ b i₀ * (∑ i ∈ s, a i)) :
--       (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) <
--         ∑ i ∈ s, a i * Real.log (a i / b i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SplitCountLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SplitCountLaw.lean#L139

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

theorem SplitCountLaw.logsum_inequality_strict{ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 < b i) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hne : a i₀ * (∑ i ∈ s, b i) ≠ b i₀ * (∑ i ∈ s, a i)) :
    (∑ i ∈ s, a i) * Real.log ((∑ i ∈ s, a i) / (∑ i ∈ s, b i)) <
      ∑ i ∈ s, a i * Real.log (a i / b i) := by sorry
