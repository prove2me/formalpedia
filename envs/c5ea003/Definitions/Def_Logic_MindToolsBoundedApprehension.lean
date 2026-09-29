-- Prove2me | Definitions.Def_Logic_MindToolsBoundedApprehension
-- name    : Logic_MindToolsBoundedApprehension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:49.90287+00:00
-- url     : https://prove2.me/theorems/a4a5e47b-0430-4426-8188-6dbee14b0454
-- title:
--   Aether Catalog definitions — Logic_MindToolsBoundedApprehension
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.MindToolsBoundedApprehension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/MindToolsBoundedApprehension.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_MindTools

/-!
# Resource-bounded apprehension: unconditional mind tools

The previous development (`Catalog/Logic/MindTools.lean`) treats "directly
apprehended by a human brain" as an undefined set-valued parameter, so every
mind-tool statement there is *conditional*: it needs a certificate consisting of
a containment and a theorem certified not to be apprehended.

This file carries out natural extensions 2, 3, 6 and 7 of the programme:

* **Bounded apprehension (2).**  We replace the psychological predicate by a
  *resource bound*: a sentence is apprehended at level `b` when it has a proof
  of size at most `b` in a fixed proof system.  This is a mathematically
  testable notion.
* **Unconditional certificates (3).**  For proof systems with finitely many
  proofs of each size and infinitely many theorems, both premises of the
  conditional theorem are *discharged*: the containment holds by definition and
  the inaccessible witness exists by counting (`isMindTool_of_infinite`).  For
  proof systems whose proofs are binary strings we get an explicit numerical
  witness: some sentence below `2 ^ (b + 1)` has no proof of size `≤ b`
  (`exists_lt_two_pow_not_apprehended`), by a pigeonhole count of the
  `2 ^ (b + 1) - 1` binary strings of length at most `b`.
* **Concrete ranks (6).**  The bounded-apprehension family is ranked by its own
  resource bound, and this ranking satisfies `MindTools.OrdinalRanks`, hence the
  hierarchy is well-founded.
* **Well-founded but not linear (7).**  A two-element family of theories is
  exhibited which is ordinal-ranked (hence well-founded) yet contains
  incomparable tools, so well-foundedness of the hierarchy does not upgrade to
  comparability.
-/

namespace MindTools
namespace Bounded

universe u

/-- A **proof system**: a type of proofs, each with a conclusion and a size.
This is the intensional datum missing from the purely extensional
`MindTools.FormalSystem`. -/
structure ProofSystem (Sentence : Type u) where
  /-- The type of formal derivations. -/
  Proof : Type
  /-- The sentence derived by a proof. -/
  conclusion : Proof → Sentence
  /-- The resource cost (length, size, time, …) of a proof. -/
  size : Proof → ℕ

variable {Sentence : Type u}

/-- The extensional theory of a proof system: the sentences it derives at all. -/
def theory (P : ProofSystem Sentence) : FormalSystem Sentence :=
  ⟨Set.range P.conclusion⟩

/-- Apprehension bounded by resource `b`: the sentences carrying a proof of size
at most `b`.  This is the mathematically testable replacement for "directly
apprehended by a human brain". -/
def apprehends (P : ProofSystem Sentence) (b : ℕ) : CognitiveProfile Sentence :=
  ⟨{s | ∃ p : P.Proof, P.size p ≤ b ∧ P.conclusion p = s}⟩



/-! ### Premise (1) is automatic for bounded apprehension -/




/-! ### Premise (2) by counting -/




/-! ### Concrete ranks for the bounded hierarchy (extension 6) -/

/-- The family of theories obtained by capping apprehension at each budget. -/
def boundedTool (P : ProofSystem Sentence) (b : ℕ) : FormalSystem Sentence :=
  ⟨(apprehends P b).direct⟩




/-! ### Binary proof systems and an explicit pigeonhole witness -/

/-- Proof systems whose derivations are binary strings, the size being the
length of the string.  Every finite proof calculus with a finite alphabet can be
coded this way. -/
def binary (c : List Bool → Sentence) : ProofSystem Sentence :=
  ⟨List Bool, c, List.length⟩

/-- The binary strings of length at most `n`. -/
def shortStrings : ℕ → Finset (List Bool)
  | 0 => {[]}
  | n + 1 =>
      insert [] (((shortStrings n).image (List.cons true)) ∪
        ((shortStrings n).image (List.cons false)))






/-! ### A fully concrete instance: the length code -/

/-- The concrete binary proof system whose conclusion is the length of the
proof: a proof of `n` is any string of `n` bits. -/
def lengthSystem : ProofSystem ℕ := binary List.length





/-! ### Well-founded does not mean linearly ordered (extension 7) -/

/-- A theory proving exactly the sentence `0`. -/
def toolZero : FormalSystem ℕ := ⟨{0}⟩

/-- A theory proving exactly the sentence `1`. -/
def toolOne : FormalSystem ℕ := ⟨{1}⟩


/-- The sample two-element family. -/
def sampleTools : Bool → FormalSystem ℕ := fun i => if i then toolZero else toolOne


end Bounded
end MindTools


