-- Prove2me | solution 1 for CertifiedEvidence.no_finite_sample_determines
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:42:57.014006+00:00
-- url     : https://prove2.me/submissions/3975f01e-a59f-4087-9778-54b976724627

-- Sol generated from MachineLearning/CertifiedEvidence/Insufficiency.lean
import Mathlib
import Definitions.Def_MachineLearning_CertifiedEvidence_Core
import Definitions.Def_MachineLearning_CertifiedEvidence_Insufficiency
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






/-! ## §2. No finite bound is a proof -/




/-! ## §3. The version space after finite evidence -/







/-! ## §4. The learning-theoretic reading: infinite VC dimension -/




open CertifiedEvidence in
theorem solution(S : Finset ℕ) (p : ℕ → Bool) :
    ∃ q : ℕ → Bool, (∀ k ∈ S, q k = p k) ∧ q ≠ p := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m ∉ S := by
    refine ⟨(S.sup id) + 1, fun hmem => ?_⟩
    have : (S.sup id) + 1 ≤ S.sup id := Finset.le_sup (f := id) hmem
    omega
  refine ⟨fun k => if k = m then !p k else p k, ?_, ?_⟩
  · intro k hk
    have : k ≠ m := fun h => hm (h ▸ hk)
    simp [this]
  · intro hcontra
    have := congrFun hcontra m
    simp at this
