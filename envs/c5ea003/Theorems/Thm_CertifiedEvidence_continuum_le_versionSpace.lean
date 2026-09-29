-- Prove2me | Theorems.Thm_CertifiedEvidence_continuum_le_versionSpace
-- name    : CertifiedEvidence.continuum_le_versionSpace
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:29:00.887166+00:00
-- url     : https://prove2.me/theorems/ddadac5f-8b2a-433c-895b-85a1eef3476a
-- title:
--   Quantitatively: the version space still has the cardinality of the continuum.
-- statement:
--   Quantitatively: the version space still has the cardinality of the continuum.
--   Finite evidence eliminates none of the hypothesis space in the sense of
--   cardinality.
--
--   ```lean
--   theorem CertifiedEvidence.continuum_le_versionSpace(p : ℕ → Bool) (N : ℕ) :
--       Cardinal.continuum ≤ Cardinal.mk (versionSpace p N) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Insufficiency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Insufficiency.lean#L137

-- Thm stub generated from MachineLearning/CertifiedEvidence/Insufficiency.lean
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

theorem CertifiedEvidence.continuum_le_versionSpace(p : ℕ → Bool) (N : ℕ) :
    Cardinal.continuum ≤ Cardinal.mk (versionSpace p N) := by sorry
