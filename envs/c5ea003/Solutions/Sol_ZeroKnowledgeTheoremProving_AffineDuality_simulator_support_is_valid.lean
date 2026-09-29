-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.AffineDuality.simulator_support_is_valid
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:06:38.077808+00:00
-- url     : https://prove2.me/submissions/667a8d59-5b6a-47bc-af01-bc495d8b8c1f

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality

/-!
# Affine Duality: Translation Hides Witnesses, Subtraction Extracts Them

This file connects two apparently opposed ideas:

* **finite-group symmetry:** translation permutes a random-tape space without
  changing its uniform distribution;
* **cryptographic proof of knowledge:** two accepting answers to opposite
  challenges determine a witness by subtraction.

These are the two directions of one affine law. Translating a random tape by the
witness gives an exact simulator (privacy), while subtracting two translated
responses recovers the witness (knowledge soundness).

The main theorem `affine_privacy_extraction_duality` says simultaneously that
any two witnesses for the same public statement produce exactly the same
multiset of public transcripts, and that accepting responses to both Boolean
challenges at one commitment reveal a witness. Privacy and extraction coexist:
privacy concerns one randomized transcript, whereas extraction compares two
correlated transcripts having the same commitment.
-/

open ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

















open ZeroKnowledgeTheoremProving.AffineDuality in
theorem solution    (s : Statement (G := G) (H := H)) (z : G) (c : Bool) :
    Accepts s (simulatedTranscript s z c) := by
  cases c <;> simp [Accepts, simulatedTranscript, challengeTerm]
