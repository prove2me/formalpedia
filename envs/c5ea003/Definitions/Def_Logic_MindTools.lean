-- Prove2me | Definitions.Def_Logic_MindTools
-- name    : Logic_MindTools
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:17.022476+00:00
-- url     : https://prove2.me/theorems/8513d39d-ad9a-42eb-933d-38d63cda86b8
-- title:
--   Aether Catalog definitions — Logic_MindTools
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.MindTools`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/MindTools.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Set.Lattice
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Basic

/-!
# Mind tools as strict extensions of direct apprehension

The informal phrase “the human brain can directly apprehend” has no canonical
mathematical definition.  This file therefore isolates it as a set-valued
parameter.  The resulting theorems state exactly which certificates are needed
for claims about a named formal system; in particular, no claim about ZFC is
smuggled in as an axiom.
-/

namespace MindTools

/-- A formal system, represented extensionally by the sentences it proves. -/
structure FormalSystem (Sentence : Type*) where
  provable : Set Sentence

/-- A cognitive profile, represented by the sentences directly apprehended. -/
structure CognitiveProfile (Sentence : Type*) where
  direct : Set Sentence

/-- A system is a mind tool when direct apprehension is a proper subset of its
provable sentences. -/
def IsMindTool {Sentence : Type*} (F : FormalSystem Sentence)
    (H : CognitiveProfile Sentence) : Prop :=
  H.direct ⊂ F.provable

/-- Proof-theoretic comparison, deliberately restricted to a fixed language. -/
def Stronger {Sentence : Type*} (F G : FormalSystem Sentence) : Prop :=
  G.provable ⊂ F.provable

/-
The simplest usable certificate for a mind tool consists of containment and
one theorem outside direct apprehension.
-/

/-
A concrete inaccessible theorem and closure of direct reasoning certify a
mind tool.
-/

/-
Strictly increasing proof strength preserves the mind-tool property.
-/

/-
Proof-theoretic strength is transitive.
-/

/-
Consequently an entire two-step hierarchy above a mind tool still extends
cognition.
-/

/-
A faithful formal version of the proposed ZFC claim: a formalized ZFC is a
mind tool once supplied with closure and a specific ZFC theorem not directly
apprehended.  Gödel incompleteness alone does not manufacture the final premise.
-/

/-- A class of problems is represented by the sentences encoding those
problems.  Uniform power means proving every sentence in that class. -/
def SolvesClass {Sentence : Type*} (F : FormalSystem Sentence)
    (problems : Set Sentence) : Prop :=
  problems ⊆ F.provable

/-
A stronger tool inherits every uniformly solved class.
-/

/-
A uniform family plus one genuinely new theorem yields strict superiority.
This captures the precise content available from “all categories at once”:
uniformity is useful only when accompanied by a theorem unavailable below.
-/

/-
The uniform categorical certificate also transports the mind-tool property
from the weaker set-theoretic tool.
-/

/-- A hierarchy indexed by `ι` is ranked by ordinals when strict tool strength
always produces a strict increase of rank. -/
def OrdinalRanks {ι Sentence : Type*} (tools : ι → FormalSystem Sentence)
    (rank : ι → Ordinal) : Prop :=
  ∀ i j, Stronger (tools j) (tools i) → rank i < rank j

/-
The proposed ordinal ranking has a rigorous consequence: there is no
infinite descending chain of tools whose direction is strict increase in
proof-theoretic strength.
-/

end MindTools


