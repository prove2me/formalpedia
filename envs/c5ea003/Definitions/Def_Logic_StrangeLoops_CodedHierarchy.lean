-- Prove2me | Definitions.Def_Logic_StrangeLoops_CodedHierarchy
-- name    : Logic_StrangeLoops_CodedHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:50.450165+00:00
-- url     : https://prove2.me/theorems/8ecd084b-ebca-45eb-a117-98bf3c0e6960
-- title:
--   Aether Catalog definitions — Logic_StrangeLoops_CodedHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.StrangeLoops.CodedHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/StrangeLoops/CodedHierarchy.lean by skeleton subtraction
import Mathlib

/-!
# Coded strange loops, Tarski's barrier, and infinitely many Gödel sentences

A diagonal lemma ranges over *representable object-language predicates*, not over every
metatheoretic predicate.  This file makes that distinction explicit by introducing a
type of predicate codes and a semantics for those codes.  This avoids the inconsistent
assumption that semantic negation of truth itself is available to diagonalization.

The main results are:

* a coded Gödel sentence is true and independent in every sound coded system;
* the predicate “is not true” cannot be represented (a Tarski-style barrier);
* if a system has rank-separated codes for its own unprovability, it contains an
  injectively indexed infinite family of independent strange loops;
* truth-preserving, proof-reflecting interpretations transport incompleteness, so a
  two-way interpretability cycle gives an explicit tangled hierarchy.
-/

noncomputable section

namespace CodedStrangeLoops

/-- A formal system whose diagonalization applies only to predicates represented by
object-language codes. -/
structure CodedDiagonalSystem where
  Sentence : Type
  Code : Type
  denotes : Code → Sentence → Prop
  codeNeg : Code → Code
  denotes_codeNeg : ∀ c s, denotes (codeNeg c) s ↔ ¬ denotes c s
  Provable : Sentence → Prop
  True_ : Sentence → Prop
  sound : ∀ s, Provable s → True_ s
  neg : Sentence → Sentence
  true_neg : ∀ s, True_ (neg s) ↔ ¬ True_ s
  diag : Code → Sentence
  diag_spec : ∀ c, True_ (diag c) ↔ denotes c (diag c)
  unprovabilityCode : Code
  unprovability_spec : ∀ s, denotes unprovabilityCode s ↔ ¬ Provable s

namespace CodedDiagonalSystem

/-- The diagonalization of the represented unprovability predicate. -/
def goedelSentence (S : CodedDiagonalSystem) : S.Sentence :=
  S.diag S.unprovabilityCode








end CodedDiagonalSystem

/-- A sufficiently expressive ranked system: for every natural rank it has a code
for unprovability, and diagonalization at that code produces a sentence of exactly
that rank.  Rank separation is the explicit syntactic resource that turns one Gödel
loop into infinitely many distinct loops. -/
structure RankedDiagonalSystem extends CodedDiagonalSystem where
  rank : Sentence → ℕ
  rankedUnprovabilityCode : ℕ → Code
  ranked_unprovability_spec :
    ∀ n s, denotes (rankedUnprovabilityCode n) s ↔ ¬ Provable s
  diag_rank : ∀ n, rank (diag (rankedUnprovabilityCode n)) = n

namespace RankedDiagonalSystem

/-- The rank-`n` Gödel sentence. -/
def rankedGoedel (S : RankedDiagonalSystem) (n : ℕ) : S.Sentence :=
  S.diag (S.rankedUnprovabilityCode n)







end RankedDiagonalSystem

/-- An interpretation preserves truth and reflects proofs.  Proof reflection is the
condition needed to transport an unprovability result backwards across translation. -/
structure Interpretation (S T : CodedDiagonalSystem) where
  translate : S.Sentence → T.Sentence
  truth_iff : ∀ s, T.True_ (translate s) ↔ S.True_ s
  reflects_proof : ∀ s, T.Provable (translate s) → S.Provable s

namespace Interpretation


end Interpretation

/-- A two-level tangled hierarchy: each formal level interprets the other. -/
structure TwoLevelTangle where
  lower : CodedDiagonalSystem
  upper : CodedDiagonalSystem
  up : Interpretation lower upper
  down : Interpretation upper lower

namespace TwoLevelTangle


end TwoLevelTangle

end CodedStrangeLoops


