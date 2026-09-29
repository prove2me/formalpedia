-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_AffineDuality
-- name    : Applications_ZeroKnowledgeTheoremProving_AffineDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:33.899825+00:00
-- url     : https://prove2.me/theorems/e34cd5f0-561f-4afd-93da-93a78bfe30b1
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_AffineDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.AffineDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/AffineDuality.lean by skeleton subtraction
import Mathlib

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

namespace ZeroKnowledgeTheoremProving.AffineDuality

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- A public additive homomorphism and target. -/
structure Statement where
  hom : G →+ H
  target : H

/-- A witness is a preimage of the public target. -/
def IsWitness (s : Statement (G := G) (H := H)) (w : G) : Prop :=
  s.hom w = s.target

/-- The public transcript of the three-move protocol. -/
structure Transcript (G H : Type*) where
  commitment : H
  challenge : Bool
  response : G
  deriving DecidableEq

/-- The witness contribution selected by the challenge bit. -/
def challengeTerm (c : Bool) (w : G) : G := if c then w else 0

/-- Honest transcript with witness `w` and random tape `r`. -/
def realTranscript (s : Statement (G := G) (H := H)) (w r : G) (c : Bool) :
    Transcript G H :=
  ⟨s.hom r, c, r + challengeTerm c w⟩

/-- Simulated transcript chosen from a freely selected response. -/
def simulatedTranscript (s : Statement (G := G) (H := H)) (z : G) (c : Bool) :
    Transcript G H :=
  ⟨s.hom z - challengeTerm c s.target, c, z⟩

/-- The verifier equation. -/
def Accepts (s : Statement (G := G) (H := H)) (t : Transcript G H) : Prop :=
  s.hom t.response = t.commitment + challengeTerm t.challenge s.target


/-- Translation by the challenged witness is a permutation of random tapes. -/
def tapeEquiv (c : Bool) (w : G) : G ≃ G where
  toFun r := r + challengeTerm c w
  invFun z := z - challengeTerm c w
  left_inv r := by simp
  right_inv z := by simp







end ZeroKnowledgeTheoremProving.AffineDuality


