-- Prove2me | Theorems.Thm_AlmostLossless_relaxed_pigeonhole_tight
-- name    : AlmostLossless.relaxed_pigeonhole_tight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:35.084018+00:00
-- url     : https://prove2.me/theorems/6ba468f7-7840-4126-b38d-adcdfade7437
-- title:
--   Tightness of the relaxed pigeonhole bound.
-- statement:
--   **Tightness of the relaxed pigeonhole bound.**  For every code size
--   `0 < M ≤ n+1` there is a scheme on the uniform source over `Fin (n+1)` whose
--   success probability is *exactly* `M/(n+1)`.  Together with `successProb_le`
--   (which gives `≤ M/(n+1)` here) this shows the ε-relaxed counting bound is
--   attained, so none of the converses above can be improved.
--
--   ```lean
--   theorem AlmostLossless.relaxed_pigeonhole_tight(n M : ℕ) (hM : 0 < M) (hMn : M ≤ n + 1) :
--       ∃ sch : Scheme (Fin (n + 1)) (Fin M),
--         successProb (uniformDist (Fin (n + 1))) sch = (M : ℝ) / (n + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessCompression.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessCompression.lean#L247

-- Thm stub generated from Bridges/AlmostLosslessCompression.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression I: Schemes and the Relaxed Pigeonhole Bound

## Bridge: Combinatorics (pigeonhole) ↔ Probability (min-entropy) ↔ Coding theory

The exact pigeonhole bound says: a code that decodes *every* source symbol
correctly needs at least `|α|` codewords.  This file develops the *relaxed*
(almost-lossless) form of that statement:

* a scheme is an encoder/decoder pair `enc : α → Code`, `dec : Code → Option α`;
* the decoder may abstain (`none`), and may in principle err silently;
* the **success set** is the set of symbols decoded exactly.

Main results:

* `enc_injOn_successSet` / `card_successSet_le_card_code` — the exact pigeonhole
  bound applies to the success set only;
* `successMass_le` — `P(success) ≤ |Code| · p_max`, i.e. the counting bound is
  relaxed by a factor governed by the min-entropy of the source;
* `card_code_ge_of_success` — the converse: to succeed with probability `1 - ε`
  one needs `|Code| ≥ (1-ε)/p_max`;
* `log_card_code_ge_of_success` — the same statement in entropy form,
  `log |Code| ≥ H_∞(μ) + log (1-ε)`;
* `exact_decoding_pigeonhole` — the classical bound is recovered at `ε = 0`.

## Impact: certified_compression_bound, almost_lossless_converse
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

variable {α : Type*} [Fintype α]

/-! ## Section 1: Mass of a finite set of source symbols -/










/-! ## Section 2: Compression schemes with an abstaining decoder -/


variable {Code : Type*}







variable [DecidableEq α]






/-! ## Section 3: The ε-relaxed counting bound -/






/-! ## Section 4: The relaxed bound is attained -/

theorem AlmostLossless.relaxed_pigeonhole_tight(n M : ℕ) (hM : 0 < M) (hMn : M ≤ n + 1) :
    ∃ sch : Scheme (Fin (n + 1)) (Fin M),
      successProb (uniformDist (Fin (n + 1))) sch = (M : ℝ) / (n + 1) := by sorry
