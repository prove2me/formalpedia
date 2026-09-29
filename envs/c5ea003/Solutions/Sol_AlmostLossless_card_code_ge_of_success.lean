-- Prove2me | solution 1 for AlmostLossless.card_code_ge_of_success
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:59:57.040607+00:00
-- url     : https://prove2.me/submissions/7d48a028-c56c-4312-a94a-ae69fcdb794f

-- Sol generated from Bridges/AlmostLosslessCompression.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_MinEntropy
import Theorems.Thm_AlmostLossless_setMass_le_card_mul_maxMass
import Theorems.Thm_NonArchInfoTheory_maxMass_pos
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


theorem mem_successSet {sch : Scheme α Code} {x : α} :
    x ∈ successSet sch ↔ sch.Succeeds x := by
  simp [successSet, Scheme.Succeeds]

/-- **Pigeonhole, localized.** The encoder is injective on the success set:
correct decoding forces distinct codewords. -/
theorem enc_injOn_successSet (sch : Scheme α Code) :
    Set.InjOn sch.enc (successSet sch) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_successSet] at hx hy
  unfold Scheme.Succeeds at hx hy
  rw [hxy] at hx
  rw [hx] at hy
  exact Option.some_inj.mp hy

/-- **Relaxed pigeonhole bound (counting form).** However small the failure
probability is allowed to be, the number of *exactly* decoded symbols never
exceeds the number of codewords. -/
theorem card_successSet_le_card_code [Fintype Code] (sch : Scheme α Code) :
    (successSet sch).card ≤ Fintype.card Code := by
  classical
  have h : (successSet sch).card ≤ (Finset.univ : Finset Code).card :=
    Finset.card_le_card_of_injOn sch.enc (fun x _ => Finset.mem_univ _)
      (enc_injOn_successSet sch)
  simpa [Finset.card_univ] using h


/-! ## Section 3: The ε-relaxed counting bound -/


/-- **The counting bound relaxes by a min-entropy factor.**
`P(success) ≤ |Code| · p_max`. -/
theorem successProb_le [Nonempty α] [Fintype Code] (μ : FinProbDist α)
    (sch : Scheme α Code) :
    successProb μ sch ≤ (Fintype.card Code : ℝ) * maxMass μ := by
  refine (setMass_le_card_mul_maxMass μ _).trans ?_
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_successSet_le_card_code sch) (le_of_lt (maxMass_pos μ))




/-! ## Section 4: The relaxed bound is attained -/



open AlmostLossless in
theorem solution[Nonempty α] [Fintype Code] (μ : FinProbDist α)
    (sch : Scheme α Code) (ε : ℝ) (h : 1 - ε ≤ successProb μ sch) :
    (1 - ε) / maxMass μ ≤ (Fintype.card Code : ℝ) := by
  have hp := maxMass_pos μ
  rw [div_le_iff₀ hp]
  calc 1 - ε ≤ successProb μ sch := h
    _ ≤ (Fintype.card Code : ℝ) * maxMass μ := successProb_le μ sch
