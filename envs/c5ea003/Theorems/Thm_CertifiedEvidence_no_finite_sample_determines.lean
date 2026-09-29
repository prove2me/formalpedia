-- Prove2me | Theorems.Thm_CertifiedEvidence_no_finite_sample_determines
-- name    : CertifiedEvidence.no_finite_sample_determines
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:30:36.864453+00:00
-- url     : https://prove2.me/theorems/ab3f66d4-ec1a-464a-9d2b-bb2e5d2e4839
-- title:
--   No finite sample determines a hypothesis.
-- statement:
--   **No finite sample determines a hypothesis.** For every finite sample `S`
--   and every hypothesis `p` there is a *different* hypothesis agreeing with `p` on
--   all of `S`. Equivalently the class `ℕ → Bool` shatters every finite set, so its
--   VC dimension is infinite and no finite sample complexity exists.
--
--   ```lean
--   theorem CertifiedEvidence.no_finite_sample_determines(S : Finset ℕ) (p : ℕ → Bool) :
--       ∃ q : ℕ → Bool, (∀ k ∈ S, q k = p k) ∧ q ≠ p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CertifiedEvidence/Insufficiency.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CertifiedEvidence/Insufficiency.lean#L156

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







/-! ## §4. The learning-theoretic reading: infinite VC dimension -/

theorem CertifiedEvidence.no_finite_sample_determines(S : Finset ℕ) (p : ℕ → Bool) :
    ∃ q : ℕ → Bool, (∀ k ∈ S, q k = p k) ∧ q ≠ p := by sorry
