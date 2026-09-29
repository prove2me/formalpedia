-- Prove2me | solution 1 for AlmostLossless.relaxed_pigeonhole_tight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:57:23.353838+00:00
-- url     : https://prove2.me/submissions/ef608e4c-e9d6-4670-9a24-e546630ccc25

-- Sol generated from Bridges/AlmostLosslessCompression.lean
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


theorem mem_successSet {sch : Scheme α Code} {x : α} :
    x ∈ successSet sch ↔ sch.Succeeds x := by
  simp [successSet, Scheme.Succeeds]




/-! ## Section 3: The ε-relaxed counting bound -/






/-! ## Section 4: The relaxed bound is attained -/



open AlmostLossless in
theorem solution(n M : ℕ) (hM : 0 < M) (hMn : M ≤ n + 1) :
    ∃ sch : Scheme (Fin (n + 1)) (Fin M),
      successProb (uniformDist (Fin (n + 1))) sch = (M : ℝ) / (n + 1) := by
  classical
  refine ⟨⟨fun x => if h : x.val < M then ⟨x.val, h⟩ else ⟨0, hM⟩,
    fun i => some (Fin.castLE hMn i)⟩, ?_⟩
  have hsucc : successSet (α := Fin (n + 1))
      ⟨fun x => if h : x.val < M then ⟨x.val, h⟩ else ⟨0, hM⟩,
        fun i => some (Fin.castLE hMn i)⟩
      = Finset.univ.filter (fun x : Fin (n + 1) => x.val < M) := by
    ext x
    simp only [mem_successSet, Scheme.Succeeds, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hx : x.val < M
    · simp [hx]
    · simp only [dif_neg hx]
      constructor
      · intro h
        have h2 := congrArg Fin.val (Option.some_inj.mp h)
        simp only [Fin.val_castLE] at h2
        omega
      · intro h; exact absurd h hx
  have hcard : (Finset.univ.filter (fun x : Fin (n + 1) => x.val < M)).card = M := by
    have : Finset.univ.filter (fun x : Fin (n + 1) => x.val < M)
        = Finset.univ.map (Fin.castLEEmb hMn) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Fin.castLEEmb_apply]
      constructor
      · intro hx
        refine ⟨⟨x.val, hx⟩, ?_⟩
        simp
      · rintro ⟨y, hy⟩
        have hylt := y.isLt
        simp only [← hy]
        simp [hylt]
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  unfold successProb setMass
  rw [hsucc]
  simp only [uniformDist, Finset.sum_const, nsmul_eq_mul, hcard, Fintype.card_fin]
  push_cast
  ring
