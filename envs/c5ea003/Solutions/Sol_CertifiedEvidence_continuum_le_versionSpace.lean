-- Prove2me | solution 1 for CertifiedEvidence.continuum_le_versionSpace
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:41:21.803645+00:00
-- url     : https://prove2.me/submissions/e3c3c46b-7c7c-401f-b589-de6ffa8f1228

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



theorem extendBeyond_mem (p : ℕ → Bool) (N : ℕ) (f : ℕ → Bool) :
    extendBeyond p N f ∈ versionSpace p N := by
  intro k _ hk
  simp [extendBeyond, hk]

theorem extendBeyond_injective (p : ℕ → Bool) (N : ℕ) :
    Function.Injective (extendBeyond p N) := by
  intro f g h
  funext m
  have := congrFun h (m + N + 1)
  simpa [extendBeyond, Nat.not_le.mpr (show N < m + N + 1 by omega),
    show m + N + 1 - (N + 1) = m by omega] using this



/-! ## §4. The learning-theoretic reading: infinite VC dimension -/




open CertifiedEvidence in
theorem solution(p : ℕ → Bool) (N : ℕ) :
    Cardinal.continuum ≤ Cardinal.mk (versionSpace p N) := by
  have hinj : Function.Injective
      (fun f : ℕ → Bool => (⟨extendBeyond p N f, extendBeyond_mem p N f⟩ :
        versionSpace p N)) := by
    intro f g h
    exact extendBeyond_injective p N (congrArg Subtype.val h)
  have h1 : Cardinal.mk (ℕ → Bool) ≤ Cardinal.mk (versionSpace p N) :=
    Cardinal.mk_le_of_injective hinj
  have h2 : Cardinal.mk (ℕ → Bool) = Cardinal.continuum := by
    rw [Cardinal.mk_arrow]
    simp [Cardinal.two_power_aleph0]
  rwa [h2] at h1
