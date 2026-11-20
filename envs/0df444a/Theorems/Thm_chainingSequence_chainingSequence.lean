-- Prove2me | Theorems.Thm_chainingSequence_chainingSequence
-- name    : chainingSequence_chainingSequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:20:55.988411+00:00
-- url     : https://prove2.me/theorems/7011a6e0-7913-45ab-816f-bad7f2cbca44
-- title:
--   chainingSequence chainingSequence
-- statement:
--   The source theorem `chainingSequence_chainingSequence` is extracted from `BrownianMotion.Continuity.Chaining`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_Chaining_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Chaining

### References
- https://arxiv.org/pdf/2107.13837.pdf Lemma 6.2
- Talagrand, The generic chaining
- Vershynin, High-Dimensional Probability (section 4.2 and chapter 8)

-/

@[expose] public section

open Metric
open scoped ENNReal NNReal

variable {E : Type*} {x y : E} {A : Set E} {C C₁ C₂ : Finset E} {ε ε₁ ε₂ : ℝ≥0}

variable [PseudoEMetricSpace E]

section Sequence

variable {ε : ℕ → ℝ≥0} {C : ℕ → Finset E} {k n : ℕ}

theorem chainingSequence_chainingSequence (n : ℕ) (hn : n ≤ k) (m : ℕ) (hm : m ≤ n) :
    chainingSequence C (chainingSequence C x k n) n m = chainingSequence C x k m := by sorry
