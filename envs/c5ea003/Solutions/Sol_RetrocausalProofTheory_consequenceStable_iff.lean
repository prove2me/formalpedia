-- Prove2me | solution 1 for RetrocausalProofTheory.consequenceStable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:06.503923+00:00
-- url     : https://prove2.me/submissions/462fb84f-e361-4039-8dfd-d68f8a60d665

-- Sol generated from Novelty/RetrocausalProofTheory.lean
import Mathlib
import Definitions.Def_Novelty_RetrocausalProofTheory

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

open RetrocausalProofTheory
















/-! ## Consequence-stable propositions -/





/-! ## Finite consequence-guided search -/








/-! ## A small arithmetic calibration -/






open RetrocausalProofTheory in
theorem solution(P : Prop) (qs : List Prop) :
    ConsequenceStable P qs ↔ (P ↔ JointlyVerified qs) := by
  constructor
  · rintro ⟨hforward, hback⟩
    constructor
    · intro hP Q hQ
      exact hforward Q hQ hP
    · exact hback
  · intro h
    constructor
    · intro Q hQ hP
      exact h.mp hP Q hQ
    · exact h.mpr
