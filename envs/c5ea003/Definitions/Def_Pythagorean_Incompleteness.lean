-- Prove2me | Definitions.Def_Pythagorean_Incompleteness
-- name    : Pythagorean_Incompleteness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-15T03:04:26.546473+00:00
-- url     : https://prove2.me/theorems/779229c1-3de6-4d7f-998b-c7de0b5b21f6
-- title:
--   Aether Catalog definitions — Pythagorean_Incompleteness
-- statement:
--   Definition bundle for the Aether Catalog module `Pythagorean.Incompleteness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Pythagorean/Incompleteness.lean by skeleton subtraction
import Mathlib

/-! # Abstract incompleteness

An *abstract formal system* is a type of sentences equipped with a negation, a provability
predicate, and a semantic truth predicate that is sound for provability and classical for
negation.  A **Gödel sentence** is a sentence asserting its own unprovability.

The theorem below is the abstract core of Gödel's first incompleteness theorem, stripped of
arithmetisation: *if a sound system has a Gödel sentence, that sentence is true and neither
it nor its negation is provable.*  Nothing about arithmetic, coding, or the diagonal lemma
is assumed — those are what produce the Gödel sentence in a concrete system; here its
existence is the hypothesis, and the conclusion is genuine undecidability.
-/

namespace ProofSpace

/-- An abstract formal system: sentences, negation, provability, and a sound truth
predicate. -/
structure FormalSystem where
  /-- The sentences of the system. -/
  Sentence : Type
  /-- Negation of a sentence. -/
  neg : Sentence → Sentence
  /-- The provability predicate. -/
  Provable : Sentence → Prop
  /-- The (semantic) truth predicate. -/
  True : Sentence → Prop
  /-- Soundness: everything provable is true. -/
  sound : ∀ s, Provable s → True s
  /-- Truth is classical for negation. -/
  true_neg : ∀ s, True (neg s) ↔ ¬ True s

namespace FormalSystem

variable (F : FormalSystem)

/-- A Gödel sentence: one that is true exactly when it is unprovable. -/
def IsGodelSentence (g : F.Sentence) : Prop := F.True g ↔ ¬ F.Provable g

/-- A sentence is undecidable when neither it nor its negation is provable. -/
def Undecidable (s : F.Sentence) : Prop := ¬ F.Provable s ∧ ¬ F.Provable (F.neg s)




end FormalSystem

end ProofSpace


