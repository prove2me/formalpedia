-- Prove2me | Definitions.Def_Bridges_TropicalSatakeCommitteePlurality
-- name    : Bridges_TropicalSatakeCommitteePlurality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:07.520184+00:00
-- url     : https://prove2.me/theorems/ff000451-68cc-4243-b677-81bd818232b0
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakeCommitteePlurality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakeCommitteePlurality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakeCommitteePlurality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Committee Plurality Robustness via Tropical Satake Certificates

This file formalizes a **committee-level plurality robustness theorem** that composes
memberwise certified robustness (e.g. from GL₃ tropical Satake top-k certificates)
into an ensemble-level winner-invariance guarantee.

## Mathematical overview

Consider a committee of `n` members, each casting a vote for one of `m` labels.
The committee winner is the label receiving the most votes (plurality winner).

The main result has two layers:

1. **Analytic / tropical layer**: each member's vote is unchanged when its score
   perturbation stays within a certified radius. This is the content of the existing
   GL₃ tropical Satake top-k robustness theorems.

2. **Discrete committee layer**: if only a bounded number `C` of members can change
   their vote, then a plurality margin strictly greater than `2C` forces the
   committee winner to remain fixed. The factor of 2 is tight: each changed member
   can simultaneously gain a vote for a competitor and lose a vote for the winner.

The key combinatorial insight is that independent per-label vote-count bounds
(`voteCount` changes by at most `C`) combine to give a vote-gap bound of `2C`:

  `voteCount v' y - voteCount v' w ≤ (voteCount v y - voteCount v w) + 2C`

The plurality stability theorem is then immediate from this gap bound.

## Main results

- `voteCount_sub_le_changed`: vote count for any label changes by at most the number
  of changed members (absolute value form).
- `voteGap_perturbation_le_changed`: the pairwise vote gap increases by at most `2C`.
- `plurality_winner_stable_of_margin_gt_twice_changed`: discrete plurality stability.
- `changedMembers_subset_unstable`: only analytically unstable members can change vote.
- `changedMembers_card_le_unstable`: cardinality consequence.
- `committee_plurality_robust_of_member_certificates`: the main abstract ensemble
  robustness theorem.
- `gl3_tropical_satake_committee_plurality_robust`: specialization to GL₃ tropical
  Satake certificates.

## Significance

This result upgrades certified robustness from a single GL₃ Hecke-score classifier
to an ensemble mechanism. The theorem isolates a discrete plurality margin principle
independent of the analytic details of tropical Satake, showing how memberwise certified
radii compose nontrivially at committee level through the cardinality of the
unstable-member set.
-/

open Finset

/-! ## Core definitions -/

/-- The number of committee members voting for label `y`. -/
def voteCount {n m : ℕ} (v : Fin n → Fin m) (y : Fin m) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => v i = y)).card

/-- The finset of members voting for label `y`. -/
def voteCountFinset {n m : ℕ} (v : Fin n → Fin m) (y : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i = y)


/-- The set of members whose vote changed under perturbation. -/
def changedMembers {n m : ℕ} (v v' : Fin n → Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ v' i)



/-- The set of analytically unstable members (perturbation exceeds certified radius). -/
noncomputable def unstableMembers {n : ℕ} (ε cert : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ¬ ε i < cert i)

/-! ## Vote count perturbation bounds -/






/-! ## Vote gap perturbation bound -/

/-
**Vote-gap perturbation bound.** The pairwise vote gap `(count y) - (count w)` can
increase by at most `2 * C` where `C` is the number of changed members. This is tight:
a member switching from `w` to `y` increases the gap by 2.
-/

/-! ## Plurality stability theorems -/

/-
**Discrete plurality stability.** If `w` beats every competitor by a margin strictly
greater than twice the number of changed members, then `w` remains the unique plurality
winner after perturbation. The factor of 2 is tight: a member switching from `w` to `y`
simultaneously increases `y`'s count and decreases `w`'s count.
-/

/-
**Corollary with explicit bound `M`.**
-/

/-! ## Bridge from analytic certificates to combinatorial bounds -/



/-! ## Main ensemble robustness theorem -/

/-
**Main theorem: Committee plurality robustness from memberwise certificates.**

Given a committee of `n` members voting among `m` labels, if:
1. each member's vote is unchanged when its perturbation is within its certified radius,
2. the plurality winner `w` beats every competitor by a margin strictly greater than
   twice the number of unstable members,

then `w` remains the unique plurality winner after perturbation.

This theorem is the correct abstract interface: the GL₃ tropical Satake theorem (or any
other memberwise robustness certificate) can be plugged in as the proof of `hstable`.

**Why the factor of 2?** Each unstable member can at worst switch its vote from `w` to
a competitor `y`, simultaneously decreasing `w`'s count by 1 and increasing `y`'s count
by 1, for a net gap change of 2 per member.
-/

/-! ## GL₃ tropical Satake specialization -/


