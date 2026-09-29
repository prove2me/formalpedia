-- Prove2me | Definitions.Def_Novelty_SplitCountLaw
-- name    : Novelty_SplitCountLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:49.36875+00:00
-- url     : https://prove2.me/theorems/93745d3c-aa17-410e-b12e-718c393085e8
-- title:
--   Aether Catalog definitions — Novelty_SplitCountLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SplitCountLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SplitCountLaw.lean by skeleton subtraction
import Mathlib

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

namespace SplitCountLaw

open Finset Real

/-- Row marginal of a finite weight table. -/
noncomputable def rowMarg {α β : Type*} [Fintype β] (p : α → β → ℝ) (a : α) : ℝ :=
  ∑ b, p a b

/-- Column marginal of a finite weight table. -/
noncomputable def colMarg {α β : Type*} [Fintype α] (p : α → β → ℝ) (b : β) : ℝ :=
  ∑ a, p a b

/-- Mutual information of a finite joint weight table, in bits. -/
noncomputable def mutualInfo {α β : Type*} [Fintype α] [Fintype β] (p : α → β → ℝ) : ℝ :=
  ∑ a, ∑ b, p a b * logb 2 (p a b / (rowMarg p a * colMarg p b))

/-- Shannon entropy (in bits) of a finite weight vector. -/
noncomputable def entropyBits {α : Type*} [Fintype α] (q : α → ℝ) : ℝ :=
  ∑ a, -(q a * logb 2 (q a))

/-! ## The log-sum inequality -/







/-! ## Data processing -/

section DPI

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq γ]

/-- Deterministic relabelling of the second coordinate. -/
noncomputable def push (p : α → β → ℝ) (g : β → γ) : α → γ → ℝ :=
  fun a c => ∑ b ∈ Finset.univ.filter (fun b => g b = c), p a b




end DPI

/-! ## The `I ≤ H(A)` cap -/

section Cap

variable {α β : Type*} [Fintype α] [Fintype β]






end Cap

/-! ## Channel decomposition `I = H(B) - H(B|A)` -/

section Channel

variable {α β : Type*} [Fintype α] [Fintype β]


end Channel

/-! ## Nonnegativity -/

section Nonneg

variable {α β : Type*} [Fintype α] [Fintype β]




end Nonneg

end SplitCountLaw


