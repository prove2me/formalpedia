-- Prove2me | Definitions.Def_Novelty_RetrocausalProofTheory
-- name    : Novelty_RetrocausalProofTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:39:32.716315+00:00
-- url     : https://prove2.me/theorems/13404e46-eeb4-4bc1-8fc9-a1ad4d26a649
-- title:
--   Aether Catalog definitions — Novelty_RetrocausalProofTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.RetrocausalProofTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/RetrocausalProofTheory.lean by skeleton subtraction
import Mathlib

/-!
# Retrocausal proof theory: a logical boundary theorem

This file studies the proposed rule “confirm `P` from verified consequences of `P`”
at the level of propositions.  Its central result is an exact characterization:
a proposition supports such a rule uniformly for every proposed consequence if and
only if the proposition was already provable.

The positive results identify the extra datum that makes backwards reasoning sound:
a *backward certificate* saying that the verified consequences jointly imply the
candidate proposition.
-/

namespace RetrocausalProofTheory

/-- Every member of `qs` is a logical consequence of `P`. -/
def AreConsequences (P : Prop) (qs : List Prop) : Prop :=
  ∀ Q ∈ qs, P → Q

/-- Every proposition in a finite list has been verified. -/
def JointlyVerified (qs : List Prop) : Prop :=
  ∀ Q ∈ qs, Q

/-- The listed propositions are propositionally coherent (joint truth is not absurd). -/
def Coherent (qs : List Prop) : Prop :=
  ¬ (JointlyVerified qs → False)

/-- A backward certificate is precisely the information needed to recover `P`. -/
def BackwardCertificate (P : Prop) (qs : List Prop) : Prop :=
  JointlyVerified qs → P












/-! ## Consequence-stable propositions -/

/-- A finite family is consequence-stable for `P` when it is both implied by
`P` and jointly sufficient to recover `P`.  This strengthens mere coherence by
recording the missing backward direction explicitly. -/
def ConsequenceStable (P : Prop) (qs : List Prop) : Prop :=
  AreConsequences P qs ∧ BackwardCertificate P qs




/-! ## Finite consequence-guided search -/

/-- A candidate passes a list of semantic checks when every check holds of it. -/
def Passes {α : Type*} (checks : List (α → Prop)) (a : α) : Prop :=
  ∀ check ∈ checks, check a

/-- Candidates remaining after all verified semantic checks are imposed. -/
noncomputable def survivingCandidates {α : Type*} [DecidableEq α]
    (candidates : Finset α) (checks : List (α → Prop)) : Finset α := by
  classical
  exact candidates.filter (Passes checks)






/-! ## A small arithmetic calibration -/

/-- Three elementary arithmetic consequences used to identify `6` among the
natural numbers below `8`.  They are formulas of first-order arithmetic and so
provide a small Peano-arithmetic calibration of consequence-guided filtering. -/
def sixChecks : List (ℕ → Prop) :=
  [fun n => 0 < n, fun n => 2 ∣ n, fun n => 3 ∣ n]




end RetrocausalProofTheory


