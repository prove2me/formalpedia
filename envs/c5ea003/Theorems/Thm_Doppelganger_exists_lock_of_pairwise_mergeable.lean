-- Prove2me | Theorems.Thm_Doppelganger_exists_lock_of_pairwise_mergeable
-- name    : Doppelganger.exists_lock_of_pairwise_mergeable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:39:30.00084+00:00
-- url     : https://prove2.me/theorems/80a7b69e-5831-4b58-9a8e-3baefd403848
-- title:
--   Doppelgänger phase-lock theorem (Černý form).
-- statement:
--   **Doppelgänger phase-lock theorem (Černý form).**  If every pair of internal states
--   can be merged by some stimulus word of length at most `L`, then a *single* stimulus word
--   of length at most `(|S| - 1) * L` phase-locks the two separated agents from *any* pair of
--   initial states.
--
--   ```lean
--   theorem Doppelganger.exists_lock_of_pairwise_mergeable[Fintype S] [Nonempty S] (δ : S → I → S) (L : ℕ)
--       (h : ∀ s t : S, ∃ w : List I, w.length ≤ L ∧ drive δ w s = drive δ w t) :
--       ∃ w : List I, w.length ≤ (Fintype.card S - 1) * L ∧ Locks δ w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Finite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Finite.lean#L131

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Finite.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
/-
# Doppelgänger Phase-Lock — the finite-state synchronization theorem

This file proves the central structural theorem of the theme: for a **finite** state
space, *pairwise* telepathy implies *global* telepathy.  In other words, if any two
individual internal states of the agent can be merged by *some* stimulus word, then a
single universal stimulus word merges **all** states simultaneously — the two
spatially separated doppelgängers phase-lock no matter how they started.

The proof is a greedy image-collapsing (Černý-style) argument, and it is quantitative:
if every pair can be merged by a word of length `≤ L`, a universal locking word of
length `≤ (|S| - 1) * L` exists.

## Main results

* `Doppelganger.rank_append_le` — the *rank* (image cardinality) of a stimulus word is
  antitone under extension: information is only ever destroyed.
* `Doppelganger.locks_iff_rank_eq_one` — locking words are exactly the rank-one words.
* `Doppelganger.exists_lock_of_pairwise_mergeable` — the quantitative synchronization
  theorem (Černý form).
* `Doppelganger.phaseLocking_iff_pairwise_mergeable` — pairwise ⟺ global phase-lock.
-/

open Doppelganger

variable {S I : Type*}


variable [Fintype S] [DecidableEq S]







variable [DecidableEq S]

theorem Doppelganger.exists_lock_of_pairwise_mergeable[Fintype S] [Nonempty S] (δ : S → I → S) (L : ℕ)
    (h : ∀ s t : S, ∃ w : List I, w.length ≤ L ∧ drive δ w s = drive δ w t) :
    ∃ w : List I, w.length ≤ (Fintype.card S - 1) * L ∧ Locks δ w := by sorry
