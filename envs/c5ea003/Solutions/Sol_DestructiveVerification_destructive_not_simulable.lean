-- Prove2me | solution 1 for DestructiveVerification.destructive_not_simulable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:41:36.848904+00:00
-- url     : https://prove2.me/submissions/5ec3c581-eca0-476f-8ab7-efd9d618887e

-- Sol generated from Combinatorics/DestructiveVerificationAlgebra.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationAlgebra
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Theorems.Thm_DestructiveVerification_Nondestructive_transcript_const
import Theorems.Thm_DestructiveVerification_fuseTest_transcript
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

/-! ## 1. Certificates form a Boolean semilattice -/





/-! ## 2. Reversibility equals restorability -/




/-! ## 3. Repeatability is not compositional -/





/-! ## 4. Certificates cannot simulate destruction -/



open DestructiveVerification in
theorem solution:
    ∃ (t : Test (Fin 2)) (d : Fin 2), ∀ c : Test (Fin 2), Nondestructive c →
      ∃ m, transcript t d m ≠ transcript c d m := by
  refine ⟨fuseTest 0, 0, fun c hc => ?_⟩
  by_contra hcon
  push_neg at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  have hc0 : transcript c 0 1 = transcript c 0 0 := hc.transcript_const 0 1
  rw [← h0, ← h1] at hc0
  have ht0 : transcript (fuseTest 0) 0 1 ≠ transcript (fuseTest 0) 0 0 := by
    rw [fuseTest_transcript, fuseTest_transcript]
    simp
  exact ht0 hc0
