-- Prove2me | solution 1 for DestructiveVerification.certificate_absorb_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:43:29.186986+00:00
-- url     : https://prove2.me/submissions/323c823b-d0e9-42a9-9a6c-a0856e4ed27a

-- Sol generated from Combinatorics/DestructiveVerificationAlgebra.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationAlgebra
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
/-
# Destructive verification V: the algebra of verification batteries

`Combinatorics.DestructiveVerification` makes tests into a monoid under
sequential composition `seq` (run one test, then the other on the residue, and
conjoin the verdicts).  This file works out the algebra of that monoid and uses
it to separate the three classes of the taxonomy *by closure properties*, which
is a sharper distinction than the pointwise counterexamples of the first file.

* **Certificates form a Boolean semilattice.**
  `DestructiveVerification.seq_self_of_nondestructive` (idempotence),
  `DestructiveVerification.nondestructive_equiv_seq` (composition of
  certificates is pointwise conjunction of verdicts), and
  `DestructiveVerification.certificate_absorb_iff` (the induced order is
  inclusion of accepted dishes).  So the sub-poset of certificates is exactly
  the Boolean lattice `2^D`, with `one` on top.
* **Destructive tests break idempotence.**
  `DestructiveVerification.exists_destructive_not_idempotent`: running the same
  destructive test twice is not the same as running it once, so no destructive
  test lies in that semilattice.
* **Reversibility = restorability.**
  `DestructiveVerification.reversible_iff_restorable`: on a finite dish space, a
  test can be undone by a follow-up test (`seq t u` nondestructive) *iff* it is
  reversible.  This is the exact algebraic content of "no information lost".
* **Repeatability is not compositional.**
  `DestructiveVerification.repeatable_not_closed_under_seq`: two repeatable
  tests — one of them even a certificate — compose to a non-repeatable test.
  Repeatable verification is therefore not a submonoid, in sharp contrast with
  the certificates.
* **Certificates cannot simulate destruction.**
  `DestructiveVerification.destructive_not_simulable`: an explicit test whose
  verdict stream is produced by no nondestructive test whatsoever, because
  certificate transcripts are constant while this one is not.

Together with the depth and realisation files this completes the separation
programme: the three classes differ pointwise, in their closure properties, and
in the verdict streams they can generate — with no hardness hypothesis anywhere.
-/

open DestructiveVerification

variable {D : Type*}

lemma verdict_seq (t₁ t₂ : Test D) (d : D) :
    verdict (seq t₁ t₂) d = (verdict t₁ d && verdict t₂ (residue t₁ d)) := rfl

/-! ## 1. Certificates form a Boolean semilattice -/





/-! ## 2. Reversibility equals restorability -/




/-! ## 3. Repeatability is not compositional -/





/-! ## 4. Certificates cannot simulate destruction -/



open DestructiveVerification in
theorem solution{c₁ c₂ : Test D} (h₁ : Nondestructive c₁)
    (h₂ : Nondestructive c₂) :
    seq c₁ c₂ = c₁ ↔ ∀ d, verdict c₁ d = true → verdict c₂ d = true := by
  constructor
  · intro h d hd
    have := congrArg (fun t => verdict t d) h
    simp only [verdict_seq, h₁ d] at this
    rw [hd] at this
    simpa using this
  · intro h
    refine ext_test (fun d => ?_) (fun d => ?_)
    · simp only [verdict_seq, h₁ d]
      cases hc : verdict c₁ d with
      | false => simp
      | true => simp [h d hc]
    · show residue c₂ (residue c₁ d) = residue c₁ d
      rw [h₂, h₁ d]
