-- Prove2me | Definitions.Def_Logic_StrangeLoops_Independence
-- name    : Logic_StrangeLoops_Independence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:59.004042+00:00
-- url     : https://prove2.me/theorems/560f2e4a-d748-4524-a7c9-6431b3934d2a
-- title:
--   Aether Catalog definitions — Logic_StrangeLoops_Independence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.StrangeLoops.Independence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/StrangeLoops/Independence.lean by skeleton subtraction
import Mathlib
import Mathlib.Logic.Function.Basic

/-!
# Strange Loops and Abstract Gödel Independence

A compact, self-contained diagonal argument.  The structure records exactly the
semantic hypotheses used: an external truth predicate, sound provability, a
truth-functional object-language negation, and a diagonal operator.  The theorem
chain starts with the self-referential sentence, proves its unprovability and
truth, upgrades this to independence, and rules out proof-producing completeness.

This is an abstract fixed-point form of the first incompleteness argument.  It
does not claim that a particular arithmetic theory satisfies the structure;
that further step requires arithmetizing syntax and proving a diagonal lemma.
-/

noncomputable section

/-- A sound formal system equipped with semantic negation and diagonalization. -/
structure DiagonalSystem where
  Sentence : Type
  Provable : Sentence → Prop
  True_ : Sentence → Prop
  sound : ∀ s, Provable s → True_ s
  neg : Sentence → Sentence
  true_neg : ∀ s, True_ (neg s) ↔ ¬ True_ s
  diag : (Sentence → Prop) → Sentence
  diag_spec : ∀ P : Sentence → Prop, True_ (diag P) ↔ P (diag P)

namespace DiagonalSystem

/-- The diagonal sentence asserting its own unprovability. -/
def goedelSentence (S : DiagonalSystem) : S.Sentence :=
  S.diag (fun s => ¬ S.Provable s)

/-
First link: the Gödel sentence is a fixed point of the operation “this
sentence is not provable,” interpreted through the truth predicate.
-/





/-- Syntactic completeness decides every sentence by a proof on one side. -/
def SyntacticallyComplete (S : DiagonalSystem) : Prop :=
  ∀ s, S.Provable s ∨ S.Provable (S.neg s)


/-- A global proof-producing decision certificate. -/
def ProofDecisionCertificate (S : DiagonalSystem) :=
  (s : S.Sentence) → S.Provable s ∨ S.Provable (S.neg s)


/-- A sentence bundled with proofs that neither it nor its negation is provable. -/
structure IndependenceWitness (S : DiagonalSystem) where
  sentence : S.Sentence
  unprovable : ¬ S.Provable sentence
  neg_unprovable : ¬ S.Provable (S.neg sentence)


end DiagonalSystem

end


