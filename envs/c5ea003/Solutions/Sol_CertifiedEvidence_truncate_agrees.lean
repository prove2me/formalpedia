-- Prove2me | solution 1 for CertifiedEvidence.truncate_agrees
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:43:26.240511+00:00
-- url     : https://prove2.me/submissions/7f141270-f98e-4d61-9228-4d55808e58a4

-- Sol generated from MachineLearning/CertifiedEvidence/Insufficiency.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Insufficiency
import Theorems.Thm_CertifiedEvidence_checkRange_of
import Theorems.Thm_CertifiedEvidence_exists_counterexample_of_checkRange_false
import Theorems.Thm_CertifiedEvidence_of_checkRange
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The exact logical strength of a finite certificate

`CertifiedEvidence.Core` gives a checker whose success on `[1, N]` is *equivalent*
to the bounded statement `∀ k ∈ [1,N], p k`.  This file measures how far that is
from the universal statement `∀ k ≥ 1, p k`, and the answer is: infinitely far,
uniformly in `N`, for a reason that is exactly the learning-theoretic one.

## Main results

* `truncate_agrees` / `truncate_fails` — the truncation operator produces, from
  any checker, a checker with the *same* evidence on `[1,N]` and an explicit
  counterexample at `N+1`.
* `finite_check_not_sound` — for every bound `N` there is a predicate passing
  the `N`-certificate and failing universally: no finite bound is a proof.
* `no_uniform_bound` — the diagonal form: there is no bound `N` that works for
  all predicates simultaneously.
* `versionSpace_infinite`, `continuum_le_versionSpace` — the *version space*
  (the set of hypotheses consistent with the evidence) after any finite amount
  of evidence still has the cardinality of the continuum.  Finite evidence
  removes no positive fraction of the hypothesis space.
* `no_finite_sample_determines` — no finite sample pins down a hypothesis: the
  class `ℕ → Bool` shatters every finite set, i.e. it has infinite VC dimension.
  This is the learning-theoretic reading of the previous item.
* `evidence_monotone_but_never_sufficient` — the two facts combined: evidence
  is monotone in `N` (more computation never hurts) yet its limit is not the
  universal statement for any single `N`.
-/


open CertifiedEvidence

/-! ## §1. Truncation: evidence-preserving sabotage -/


theorem truncate_apply_of_le {p : ℕ → Bool} {N k : ℕ} (h : k ≤ N) :
    truncate p N k = p k := by
  simp [truncate, h]




/-! ## §2. No finite bound is a proof -/




/-! ## §3. The version space after finite evidence -/







/-! ## §4. The learning-theoretic reading: infinite VC dimension -/




open CertifiedEvidence in
theorem solution(p : ℕ → Bool) (N lo : ℕ) :
    checkRange (truncate p N) lo N = checkRange p lo N := by
  by_cases h : checkRange p lo N = true
  · rw [h]
    refine checkRange_of _ lo N fun k hk hk' => ?_
    rw [truncate_apply_of_le hk']
    exact of_checkRange h hk hk'
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.eq_false_iff]
    intro hc
    obtain ⟨k, hk1, hk2, hk3⟩ := exists_counterexample_of_checkRange_false h
    have := of_checkRange hc hk1 hk2
    rw [truncate_apply_of_le hk2, hk3] at this
    exact Bool.noConfusion this
