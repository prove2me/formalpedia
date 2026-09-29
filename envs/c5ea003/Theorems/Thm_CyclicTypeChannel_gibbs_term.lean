-- Prove2me | Theorems.Thm_CyclicTypeChannel_gibbs_term
-- name    : CyclicTypeChannel.gibbs_term
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:23:26.644829+00:00
-- url     : https://prove2.me/theorems/645e4ab6-d313-4090-8e63-95387eacbf6d
-- title:
--   Gibbs term
-- statement:
--   Formal statement of `CyclicTypeChannel.gibbs_term` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CyclicTypeChannel.gibbs_term{q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hp' : q ≠ 0 → 0 < p) :
--       (q - p) / Real.log 2 ≤ q * Real.logb 2 (q / p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelNonneg.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelNonneg.lean#L22

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

theorem CyclicTypeChannel.gibbs_term{q p : ℝ} (hq : 0 ≤ q) (hp : 0 ≤ p) (hp' : q ≠ 0 → 0 < p) :
    (q - p) / Real.log 2 ≤ q * Real.logb 2 (q / p) := by sorry
