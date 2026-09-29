-- Prove2me | solution 1 for Chrono.TraceExpr.normalize_sound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:38.66805+00:00
-- url     : https://prove2.me/submissions/56b77819-1175-46d1-b0ba-ae590061dbde

-- Sol generated from Bridges/ChronometricTrace.lean
import Mathlib
import Definitions.Def_Bridges_ChronometricCore
import Definitions.Def_Bridges_ChronometricTrace
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Trace Syntax and Normalization for Chronometric Semirings

Bridge: connects finite-trace canonicalization to post_quantum_trace_canonicalization.
Bridge: connects idempotent semiring trace aggregation to lipschitz_certified_robustness.
Bridge: connects quantum_timeRev_normalization to effective symbolic computation.

## Main results

* `TraceExpr.eval_rev` — evaluation commutes with time reversal
* `TraceExpr.normalize_sound` — normalization preserves semantics
* `post_quantum_trace_canonicalization_bound` — normal form size ≤ 2^size
-/

set_option maxHeartbeats 800000

universe u v

open Chrono

open Chrono

/-! ## Section 1: Trace expression syntax -/





/-! ## Section 2: Semantic evaluation -/

variable {α : Type u} {R : Type v} [ChronometricSemiring R]







/-! ## Section 3: Normalization -/






/-! ## Section 4: Soundness of normalization -/

/-- Evaluation of concatenated normal forms is additive. -/
theorem evalNF_append (σ : α → R) (nf1 nf2 : TraceNormalForm α) :
    evalNF σ (nf1 ++ nf2) = evalNF σ nf1 + evalNF σ nf2 := by
  induction nf1 with
  | nil => simp [evalNF]
  | cons w ws ih =>
    show evalWord σ w + evalNF σ (ws ++ nf2) = (evalWord σ w + evalNF σ ws) + evalNF σ nf2
    rw [ih, add_assoc]

/-- Evaluation of concatenated words is multiplicative. -/
theorem evalWord_append (σ : α → R) (w1 w2 : TraceWord α) :
    evalWord σ (w1 ++ w2) = evalWord σ w1 * evalWord σ w2 := by
  induction w1 with
  | nil => simp [evalWord, one_mul]
  | cons s ws ih =>
    show evalSignedAtom σ s * evalWord σ (ws ++ w2) = (evalSignedAtom σ s * evalWord σ ws) * evalWord σ w2
    rw [ih, mul_assoc]

/-- Evaluation of mapped-append normal form. -/
theorem evalNF_map_append (σ : α → R) (w : TraceWord α) (nf : TraceNormalForm α) :
    evalNF σ (nf.map (fun w2 => w ++ w2)) = evalWord σ w * evalNF σ nf := by
  induction nf with
  | nil => simp [evalNF, mul_zero]
  | cons w2 ws ih =>
    show evalWord σ (w ++ w2) + evalNF σ (ws.map (fun w2 => w ++ w2)) = evalWord σ w * (evalWord σ w2 + evalNF σ ws)
    rw [evalWord_append, ih, mul_add]

/-- Evaluation of mulNF equals the product. -/
theorem evalNF_mulNF (σ : α → R) (nf1 nf2 : TraceNormalForm α) :
    evalNF σ (mulNF nf1 nf2) = evalNF σ nf1 * evalNF σ nf2 := by
  induction nf1 with
  | nil => simp [mulNF, evalNF, zero_mul]
  | cons w ws ih =>
    show evalNF σ (nf2.map (fun w2 => w ++ w2) ++ mulNF ws nf2) =
         (evalWord σ w + evalNF σ ws) * evalNF σ nf2
    rw [evalNF_append, evalNF_map_append, ih, add_mul]

/-- Evaluation of a flipped signed atom. -/
theorem evalSignedAtom_flip (σ : α → R) (s : SignedAtom α) :
    evalSignedAtom σ s.flip = ChronometricSemiring.timeRev (evalSignedAtom σ s) := by
  cases s with
  | fwd a => rfl
  | bwd a =>
    show σ a = ChronometricSemiring.timeRev (ChronometricSemiring.timeRev (σ a))
    exact (ChronometricSemiring.timeRev_involutive (σ a)).symm

/-
Evaluation of a reversed word equals timeRev of the original.
-/
theorem evalWord_revWord (σ : α → R) (w : TraceWord α) :
    evalWord σ (revWord w) = ChronometricSemiring.timeRev (evalWord σ w) := by
  induction' w with s w ih;
  · exact ( ‹ChronometricSemiring R›.timeRev_one ) ▸ rfl;
  · unfold revWord; simp +decide [ *, evalWord ] ;
    rw [ evalWord_append ];
    convert congr_arg ( fun x => x * evalSignedAtom σ s.flip ) ih using 1;
    · congr;
      exact show evalSignedAtom σ s.flip * 1 = evalSignedAtom σ s.flip from by rw [ mul_one ] ;
    · rw [ evalSignedAtom_flip, ChronometricSemiring.timeRev_mul ]

/-- Evaluation of a reversed normal form. -/
theorem evalNF_revNF (σ : α → R) (nf : TraceNormalForm α) :
    evalNF σ (revNF nf) = ChronometricSemiring.timeRev (evalNF σ nf) := by
  induction nf with
  | nil =>
    show (0 : R) = ChronometricSemiring.timeRev 0
    exact ChronometricSemiring.timeRev_zero.symm
  | cons w ws ih =>
    show evalWord σ (revWord w) + evalNF σ (ws.map revWord) =
      ChronometricSemiring.timeRev (evalWord σ w + evalNF σ ws)
    have : evalNF σ (ws.map revWord) = evalNF σ (revNF ws) := rfl
    rw [this, evalWord_revWord, ih, ChronometricSemiring.timeRev_add]


/-! ## Section 5: Size measures and complexity bounds -/



/-
The size of mulNF is the product of sizes.
-/


/-
**Post-quantum trace canonicalization bound**:
`‖normalize(e)‖ ≤ 2^(size(e))`.
Bridge: connects to lipschitz_certified_robustness_trace_bound.
-/


/-
**For mul-free expressions, normalization is linear.**
Bridge: connects to lipschitz_certified_robustness_trace_bound.
-/

/-! ## Section 6: Decidable equivalence -/







open Chrono in
theorem solution(σ : α → R) (e : TraceExpr α) :
    evalNF σ e.normalize = e.eval σ := by
  induction e with
  | zero => rfl
  | one =>
    show (1 : R) + 0 = 1
    exact add_zero 1
  | atom a =>
    show evalSignedAtom σ (.fwd a) * 1 + 0 = σ a
    simp [evalSignedAtom, mul_one, add_zero]
  | add e f ihe ihf =>
    show evalNF σ (e.normalize ++ f.normalize) = e.eval σ + f.eval σ
    rw [evalNF_append, ihe, ihf]
  | mul e f ihe ihf =>
    show evalNF σ (mulNF e.normalize f.normalize) = e.eval σ * f.eval σ
    rw [evalNF_mulNF, ihe, ihf]
  | rev e ih =>
    show evalNF σ (revNF e.normalize) = ChronometricSemiring.timeRev (e.eval σ)
    rw [evalNF_revNF, ih]
