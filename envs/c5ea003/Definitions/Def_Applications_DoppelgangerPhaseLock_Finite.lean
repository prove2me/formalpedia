-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
-- name    : Applications_DoppelgangerPhaseLock_Finite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:42:34.125781+00:00
-- url     : https://prove2.me/theorems/d3a3ef05-0bda-4765-9006-d6092209eaad
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Finite
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Finite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Finite.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
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

namespace Doppelganger

variable {S I : Type*}

section Rank

variable [Fintype S] [DecidableEq S]

/-- The **rank** of a stimulus word: how many distinct internal states remain
distinguishable after the agents have observed it. -/
def rank (δ : S → I → S) (w : List I) : ℕ := (Finset.univ.image (drive δ w)).card




end Rank

section Synchronization

variable [DecidableEq S]





end Synchronization

section AbsoluteBound

/-! ### An absolute (Černý-style) bound on the phase-lock time

So far the locking time was expressed in terms of an *assumed* bound `L` on pairwise
merging times.  We now remove that assumption: a pigeonhole argument in the **pair
automaton** `S × S` shows that a mergeable pair is always mergeable within `|S|²`
stimuli, whence an unconditional cubic bound on the doppelgänger phase-lock time.
-/




end AbsoluteBound

end Doppelganger


