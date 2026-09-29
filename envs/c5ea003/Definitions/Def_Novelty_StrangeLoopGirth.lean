-- Prove2me | Definitions.Def_Novelty_StrangeLoopGirth
-- name    : Novelty_StrangeLoopGirth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:43:02.946385+00:00
-- url     : https://prove2.me/theorems/d14a01c8-dfa4-4b19-b4ac-8014f1a84ff6
-- title:
--   Aether Catalog definitions — Novelty_StrangeLoopGirth
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StrangeLoopGirth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StrangeLoopGirth.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# I Am a Strange Loop, Part VI: The Girth of a Tangled Hierarchy

Part II showed that an oriented (asymmetric) hierarchy admits no strange loop of
length `1` or `2`, while genuine loops appear at length `3` — the minimum
"strange-loop length".  Here we go deeper and compute the loop length exactly for
a tunable family of hierarchies, exhibiting *girth* as a controllable resource.

We study the cyclic **successor** relation `a ↦ a + 1` on `ZMod n`, the
prototypical tangled hierarchy (rock-paper-scissors when `n = 3`).  A closed walk
of length `k` in this relation forces the running index to advance by `k` and
return to its start, which is possible exactly when `n ∣ k`.  Consequently:

* a strange loop of length `n` always exists (`succ_loop_exists`);
* every closed loop has length divisible by `n` (`succ_loop_dvd`);
* hence the **minimum strange-loop length ("girth") is exactly `n`**
  (`succ_min_loop_length`).

This bridges the **combinatorics of tangled hierarchies** with the **arithmetic
of cyclic groups**: the depth of self-reference realizable in a hierarchy is
governed by a divisibility condition, and can be tuned to any prescribed value
`n ≥ 3`.  The generic bound "girth ≥ 3" of Part II becomes the exact identity
"girth = n" for these relations.

This file is fully self-contained.
-/

namespace StrangeLoop.Girth

open Relation

/-! ## Closed loops indexed by natural numbers with wraparound -/

/-- A **closed loop of length `k`** in a relation `R`: an assignment `v` of
levels to positions `0, 1, …, k-1` with consecutive positions `R`-related and
the last position wrapping back to the first (index arithmetic modulo `k`). -/
def IsLoopN {V : Type*} (R : V → V → Prop) (k : ℕ) (v : ℕ → V) : Prop :=
  0 < k ∧ ∀ i, i < k → R (v i) (v ((i + 1) % k))

/-! ## The successor relation on `ZMod n` -/

/-- The cyclic successor relation `a ↦ a + 1` on `ZMod n`. -/
def succR (n : ℕ) : ZMod n → ZMod n → Prop := fun a b => b = a + 1





/-! ## Examples and boundary cases -/

/-! ## Synthesis

Part II bounded the girth of any oriented hierarchy from below by `3`.  Here the
successor relation on `ZMod n` realizes girth *exactly* `n`, tied to the cyclic
group's order through a divisibility law.  Tangled hierarchies thus carry a
precise arithmetic invariant — their girth — and Hofstadter's "the loop must run
through the hierarchy and return" is quantified: the shortest return has length
equal to the number of levels the cycle spans. -/

end StrangeLoop.Girth

/-
-- !-- Lab Notes -- !--

Hypothesis (Hypothesizer): Part II's generic bound "strange-loop length ≥ 3" for
oriented hierarchies should sharpen to an *exact* value for structured
hierarchies, controlled by an arithmetic invariant, making self-referential depth
a tunable resource.

Experiment (Experimenter): Modeled the cyclic successor relation `a ↦ a+1` on
`ZMod n`. Proved existence of a length-`n` loop (identity assignment) and, via an
affine-chain induction, that every closed loop has length divisible by `n`. Hence
girth `= n`.

Analysis (Analyst): The divisibility law `n ∣ k` is the crux; it follows because
traversing a closed walk advances the index by `k` and must return to start,
forcing `k ≡ 0 (mod n)`. The `n = 3` case reproduces Part II ("no length-2 loop"
because `3 ∤ 2`), confirming the new result strictly generalizes the old.

Critique (Critic): Verified no circularity — `girth_is_group_order` and
`succ_min_loop_length` are built from `succ_loop_dvd`/`succ_loop_exists`, both
proved earlier without self-reference. The loop definition uses honest index
wraparound `(i+1) % k`, so the boundary edge is not swept under the rug; the
example `¬ ∃ v, IsLoopN (succR 3) 2 v` exercises exactly that edge.

Synthesis (PI): Tangled hierarchies carry a precise arithmetic fingerprint — their
girth equals the cyclic group's order. Hofstadter's "the loop runs through the
hierarchy and returns" is quantified: the shortest return spans exactly `n`
levels.
-/


