-- Prove2me | Theorems.Thm_CyclicTypeChannel_condEnt_eq_joint
-- name    : CyclicTypeChannel.condEnt_eq_joint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:23:21.081598+00:00
-- url     : https://prove2.me/theorems/89e15939-d38f-42d0-ac40-fe772245783f
-- title:
--   Cond ent eq joint
-- statement:
--   Formal statement of `CyclicTypeChannel.condEnt_eq_joint` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CyclicTypeChannel.condEnt_eq_joint(s : Finset α) (g : α → β) (k : α → γ) :
--       condEnt s g k = ∑ c ∈ s.image k,
--         (((#{x ∈ s | k x = c} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
--           - (∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ)
--               * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) / s.card) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelNonneg.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelNonneg.lean#L130

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

theorem CyclicTypeChannel.condEnt_eq_joint(s : Finset α) (g : α → β) (k : α → γ) :
    condEnt s g k = ∑ c ∈ s.image k,
      (((#{x ∈ s | k x = c} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
        - (∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ)
            * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) / s.card) := by sorry
