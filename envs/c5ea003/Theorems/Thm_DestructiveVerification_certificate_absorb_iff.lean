-- Prove2me | Theorems.Thm_DestructiveVerification_certificate_absorb_iff
-- name    : DestructiveVerification.certificate_absorb_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:09:14.866314+00:00
-- url     : https://prove2.me/theorems/1f671c30-dad7-4c4e-a3d6-f06723547cea
-- title:
--   The natural order on certificates: `seq c₁ c₂ = c₁` says exactly that every
-- statement:
--   The natural order on certificates: `seq c₁ c₂ = c₁` says exactly that every
--   dish accepted by `c₁` is accepted by `c₂`, i.e. `c₁` is the stronger check.
--
--   ```lean
--   theorem DestructiveVerification.certificate_absorb_iff{c₁ c₂ : Test D} (h₁ : Nondestructive c₁)
--       (h₂ : Nondestructive c₂) :
--       seq c₁ c₂ = c₁ ↔ ∀ d, verdict c₁ d = true → verdict c₂ d = true := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationAlgebra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationAlgebra.lean#L59

-- Thm stub generated from Combinatorics/DestructiveVerificationAlgebra.lean
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

/-! ## 1. Certificates form a Boolean semilattice -/

theorem DestructiveVerification.certificate_absorb_iff{c₁ c₂ : Test D} (h₁ : Nondestructive c₁)
    (h₂ : Nondestructive c₂) :
    seq c₁ c₂ = c₁ ↔ ∀ d, verdict c₁ d = true → verdict c₂ d = true := by sorry
