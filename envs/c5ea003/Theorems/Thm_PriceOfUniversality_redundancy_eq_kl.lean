-- Prove2me | Theorems.Thm_PriceOfUniversality_redundancy_eq_kl
-- name    : PriceOfUniversality.redundancy_eq_kl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:22:19.310257+00:00
-- url     : https://prove2.me/theorems/70b2f8ab-964e-4d65-baeb-aff1c1359cb7
-- title:
--   Redundancy decomposes as a relative entropy against the coding distribution
-- statement:
--   Redundancy decomposes as a relative entropy against the coding distribution
--   `2 ^ (-L a)`.
--
--   ```lean
--   theorem PriceOfUniversality.redundancy_eq_kl{p : A → ℝ} (hp : IsPMF p) (L : A → ℕ) :
--       redundancy p L = kl p (fun a => ((2:ℝ)⁻¹) ^ (L a)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/UniversalRedundancyCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/UniversalRedundancyCore.lean#L94

-- Thm stub generated from Novelty/UniversalRedundancyCore.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
/-
# The price of universality, I: codes, entropy and per-source redundancy

This file sets up the basic apparatus used throughout the *price of universality*
development:

* length functions and the Kraft inequality (`IsCode`),
* Shannon entropy, relative entropy (Kullback-Leibler divergence) and
  expected code length, all measured in **bits**,
* Gibbs' inequality (`kl_nonneg`),
* the source coding lower bound `entropy_le_expLen`, i.e. *redundancy is
  nonnegative*, and
* the Shannon code, showing the per-source optimum is within one bit of the
  entropy (`exists_code_redundancy_le_one`).

Everything is finitary and completely self-contained.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]

/-! ## Codes -/




/-! ## Information quantities (in bits) -/





/-! ## Gibbs' inequality -/

    

/-! ## Source coding lower bound -/

theorem PriceOfUniversality.redundancy_eq_kl{p : A → ℝ} (hp : IsPMF p) (L : A → ℕ) :
    redundancy p L = kl p (fun a => ((2:ℝ)⁻¹) ^ (L a)) := by sorry
