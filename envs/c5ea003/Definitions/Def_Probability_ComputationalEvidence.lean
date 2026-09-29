-- Prove2me | Definitions.Def_Probability_ComputationalEvidence
-- name    : Probability_ComputationalEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:08.390798+00:00
-- url     : https://prove2.me/theorems/2f0963e3-cfa7-4aff-9158-36b34ab1becf
-- title:
--   Aether Catalog definitions — Probability_ComputationalEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ComputationalEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ComputationalEvidence.lean by skeleton subtraction
import Mathlib
/-
# Executable small-case evidence for square-lattice self-avoiding walks

This independent finite enumerator represents a walk by a list of cardinal
steps, computes all visited vertices, and filters by pairwise distinctness.
The final theorem kernel-checks the classical initial count sequence through
length six: `1, 4, 12, 36, 100, 284, 780`.
-/


namespace SAWResearchEvidence

abbrev Point := ℤ × ℤ

inductive Step where
  | north | south | east | west
  deriving DecidableEq, Repr

/-- Apply one cardinal step. -/
def move : Point → Step → Point
  | (x, y), .north => (x, y + 1)
  | (x, y), .south => (x, y - 1)
  | (x, y), .east => (x + 1, y)
  | (x, y), .west => (x - 1, y)

/-- Vertices visited by a step list, including the origin. -/
def visitedVertices (w : List Step) : List Point :=
  w.scanl move (0, 0)

/-- Executable self-avoidance test. -/
def isSelfAvoiding (w : List Step) : Bool :=
  decide (visitedVertices w).Nodup

/-- All cardinal-step words of a fixed length. -/
def allWalks : ℕ → List (List Step)
  | 0 => [[]]
  | n + 1 => (allWalks n).flatMap fun w =>
      [.north :: w, .south :: w, .east :: w, .west :: w]

/-- Brute-force number of square-lattice SAWs of length `n`. -/
def enumeratedCount (n : ℕ) : ℕ :=
  ((allWalks n).filter isSelfAvoiding).length



end SAWResearchEvidence


