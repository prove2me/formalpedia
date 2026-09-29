-- Prove2me | Theorems.Thm_CyclicTypeChannel_mutInfo_nonneg
-- name    : CyclicTypeChannel.mutInfo_nonneg
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:30:35.304244+00:00
-- url     : https://prove2.me/theorems/32a50be9-b474-479a-983f-3dbd27631d90
-- title:
--   Non-negativity of the counting mutual information (Gibbs' inequality):
-- statement:
--   **Non-negativity of the counting mutual information** (Gibbs' inequality):
--   conditioning on a second read-out never increases the average uncertainty.
--
--   ```lean
--   theorem CyclicTypeChannel.mutInfo_nonneg(s : Finset α) (g : α → β) (k : α → γ) : 0 ≤ mutInfo s g k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelNonneg.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelNonneg.lean#L243

-- Thm stub generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
/-
# Non-negativity of the counting mutual information

The channel quantities used for the cyclic splitting-type channel are honest
information-theoretic objects: this file proves the Gibbs inequality for the
counting framework, i.e. `I(g ; k) ≥ 0` for every pair of read-outs of a finite
uniform source, and derives the sandwich `0 ≤ I(g ; k) ≤ H(g)`.

The proof is the classical one: `I` is the Kullback–Leibler divergence between
the joint law and the product of the marginals, and `log t ≤ t - 1`.
-/

open CyclicTypeChannel

open Finset

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-! ## 1. The analytic core -/



/-! ## 2. The joint count array of two read-outs -/


variable (s : Finset α) (g : α → β) (k : α → γ)







/-! ## 3. Non-negativity -/

theorem CyclicTypeChannel.mutInfo_nonneg(s : Finset α) (g : α → β) (k : α → γ) : 0 ≤ mutInfo s g k := by sorry
