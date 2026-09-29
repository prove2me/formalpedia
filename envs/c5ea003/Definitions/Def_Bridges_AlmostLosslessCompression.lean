-- Prove2me | Definitions.Def_Bridges_AlmostLosslessCompression
-- name    : Bridges_AlmostLosslessCompression
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:02.067657+00:00
-- url     : https://prove2.me/theorems/8f67ac7a-e1c6-4524-a2ee-6935b69c73c9
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessCompression
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessCompression`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessCompression.lean by skeleton subtraction
import Mathlib
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

namespace AlmostLossless

variable {α : Type*} [Fintype α]

/-! ## Section 1: Mass of a finite set of source symbols -/

/-- The probability mass of a finite set of source symbols. -/
noncomputable def setMass (μ : FinProbDist α) (S : Finset α) : ℝ :=
  ∑ x ∈ S, μ.mass x









/-! ## Section 2: Compression schemes with an abstaining decoder -/

/-- A compression scheme: an encoder into a code space, and a decoder that is
allowed to abstain by returning `none`. -/
structure Scheme (α : Type*) (Code : Type*) where
  /-- The encoder. -/
  enc : α → Code
  /-- The decoder, allowed to report failure. -/
  dec : Code → Option α

variable {Code : Type*}

/-- The scheme decodes `x` correctly. -/
def Scheme.Succeeds (sch : Scheme α Code) (x : α) : Prop :=
  sch.dec (sch.enc x) = some x

/-- The scheme *silently corrupts* `x`: it returns a confident but wrong answer. -/
def Scheme.SilentError (sch : Scheme α Code) (x : α) : Prop :=
  ∃ y, sch.dec (sch.enc x) = some y ∧ y ≠ x

/-- A scheme *never corrupts silently* when every confident answer is correct;
failures are then always detected (reported as `none`). -/
def Scheme.NeverSilent (sch : Scheme α Code) : Prop :=
  ∀ x, ¬ sch.SilentError x


instance Scheme.decidableSucceeds [DecidableEq α] (sch : Scheme α Code) :
    DecidablePred sch.Succeeds := fun _ => by unfold Scheme.Succeeds; infer_instance

instance Scheme.decidableSilentError [DecidableEq α] (sch : Scheme α Code) :
    DecidablePred sch.SilentError := fun _ => by unfold Scheme.SilentError; infer_instance

variable [DecidableEq α]

/-- The set of source symbols the scheme decodes exactly. -/
def successSet (sch : Scheme α Code) : Finset α :=
  Finset.univ.filter (fun x => sch.dec (sch.enc x) = some x)





/-! ## Section 3: The ε-relaxed counting bound -/

/-- The success probability of a scheme. -/
noncomputable def successProb (μ : FinProbDist α) (sch : Scheme α Code) : ℝ :=
  setMass μ (successSet sch)





/-! ## Section 4: The relaxed bound is attained -/


end AlmostLossless


