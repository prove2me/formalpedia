-- Prove2me | Definitions.Def_Novelty_UniversalRedundancyCore
-- name    : Novelty_UniversalRedundancyCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:37.860445+00:00
-- url     : https://prove2.me/theorems/b13612ab-9ecd-4443-9163-1a9828e74d63
-- title:
--   Aether Catalog definitions — Novelty_UniversalRedundancyCore
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniversalRedundancyCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniversalRedundancyCore.lean by skeleton subtraction
import Mathlib
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

namespace PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A]

/-! ## Codes -/

/-- The Kraft sum `∑ 2 ^ (-L a)` of a length function. -/
noncomputable def kraftSum (L : A → ℕ) : ℝ := ∑ a, ((2 : ℝ) ⁻¹) ^ (L a)

/-- A length function is a *code* when it satisfies Kraft's inequality; by the
Kraft-McMillan theorem this is exactly the constraint satisfied by uniquely
decodable codes. -/
def IsCode (L : A → ℕ) : Prop := kraftSum L ≤ 1

/-- A probability mass function on a finite alphabet. -/
structure IsPMF (p : A → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  total : ∑ a, p a = 1

/-! ## Information quantities (in bits) -/

/-- Shannon entropy, in bits. -/
noncomputable def entropy (p : A → ℝ) : ℝ := ∑ a, -(p a * logb 2 (p a))

/-- Relative entropy (KL divergence), in bits. -/
noncomputable def kl (p q : A → ℝ) : ℝ := ∑ a, p a * logb 2 (p a / q a)

/-- Expected code length, in bits. -/
noncomputable def expLen (p : A → ℝ) (L : A → ℕ) : ℝ := ∑ a, p a * (L a : ℝ)

/-- The redundancy of the code `L` on the source `p`: the number of bits spent
above the entropy of `p`. -/
noncomputable def redundancy (p : A → ℝ) (L : A → ℕ) : ℝ := expLen p L - entropy p

/-! ## Gibbs' inequality -/

    

/-! ## Source coding lower bound -/




/-! ## The Shannon code: the per-source optimum costs at most one extra bit -/


/-- The Shannon code for a source `p`: give `a` the length `⌈log₂ (1 / p a)⌉`. -/
noncomputable def shannonCode (p : A → ℝ) : A → ℕ := fun a => ⌈-logb 2 (p a)⌉₊




end PriceOfUniversality


