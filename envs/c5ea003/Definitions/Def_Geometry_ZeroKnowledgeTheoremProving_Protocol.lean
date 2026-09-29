-- Prove2me | Definitions.Def_Geometry_ZeroKnowledgeTheoremProving_Protocol
-- name    : Geometry_ZeroKnowledgeTheoremProving_Protocol
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:01:32.604414+00:00
-- url     : https://prove2.me/theorems/6c57dbd2-7459-4451-b982-5e87a9825041
-- title:
--   Aether Catalog definitions — Geometry_ZeroKnowledgeTheoremProving_Protocol
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.ZeroKnowledgeTheoremProving.Protocol`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/ZeroKnowledgeTheoremProving/Protocol.lean by skeleton subtraction
import Mathlib

/-!
# A Perfect Honest-Verifier Zero-Knowledge Identification Protocol

This file gives an information-theoretic model of a three-move identification
protocol for a public homomorphism `φ : G →+ H`.  A witness `w` for the public
statement `y` satisfies `φ w = y`.  The prover commits with `φ r`, answers a
Boolean challenge with either `r` or `r + w`, and the verifier checks the
corresponding homomorphism equation.

Rather than appealing informally to "seeing one random proof step", perfect
honest-verifier zero knowledge is expressed by an explicit bijection of random
tapes: translating `r` by the challenged witness turns every real transcript
into the simulator's transcript.  The same development proves completeness and
special soundness (two answers to opposite challenges extract a witness).
-/

namespace ZeroKnowledgeIdentification

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

/-- Public parameters and public statement for the protocol. -/
structure Statement where
  hom : G →+ H
  target : H

/-- A witness is a preimage of the public target. -/
def IsWitness (s : Statement (G := G) (H := H)) (w : G) : Prop :=
  s.hom w = s.target

/-- The public transcript of one protocol execution. -/
structure Transcript (G H : Type*) where
  commitment : H
  challenge : Bool
  response : G
  deriving DecidableEq

/-- The witness contribution to an answer for a Boolean challenge. -/
def challengeTerm (c : Bool) (w : G) : G := if c then w else 0

/-- Transcript produced by an honest prover with witness `w` and random tape `r`. -/
def realTranscript (s : Statement (G := G) (H := H)) (w r : G) (c : Bool) :
    Transcript G H :=
  ⟨s.hom r, c, r + challengeTerm c w⟩

/-- Transcript produced by the simulator from a freely selected response `z`. -/
def simulatedTranscript (s : Statement (G := G) (H := H)) (z : G) (c : Bool) :
    Transcript G H :=
  ⟨s.hom z - challengeTerm c s.target, c, z⟩

/-- The verifier's acceptance predicate. -/
def Accepts (s : Statement (G := G) (H := H)) (t : Transcript G H) : Prop :=
  s.hom t.response = t.commitment + challengeTerm t.challenge s.target



/-- Translation by the challenge-dependent witness term is a bijection of random
    tapes.  This is the measure-preserving reindexing behind perfect zero knowledge. -/
def tapeEquiv (c : Bool) (w : G) : G ≃ G where
  toFun r := r + challengeTerm c w
  invFun z := z - challengeTerm c w
  left_inv r := by simp
  right_inv z := by simp






end ZeroKnowledgeIdentification


