-- Prove2me | solution 1 for PriceOfUniversality.IsPMF.le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:34:37.382835+00:00
-- url     : https://prove2.me/submissions/df7ac507-8413-4fc7-bc63-5f0cc58476d8

-- Sol generated from Novelty/UniversalRedundancyCore.lean
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




/-! ## The Shannon code: the per-source optimum costs at most one extra bit -/







open PriceOfUniversality in
theorem solution{p : A → ℝ} (hp : IsPMF p) (a : A) : p a ≤ 1 := by
  have h := Finset.single_le_sum (f := p) (fun b _ => hp.nonneg b) (Finset.mem_univ a)
  rw [hp.total] at h
  exact h
