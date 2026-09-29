-- Prove2me | Definitions.Def_Shared_NeuralCoding_SeidelTriangleHolonomy
-- name    : Shared_NeuralCoding_SeidelTriangleHolonomy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:46.621601+00:00
-- url     : https://prove2.me/theorems/567d0d4b-fa0b-47c4-85a1-9d4720718654
-- title:
--   Aether Catalog definitions — Shared_NeuralCoding_SeidelTriangleHolonomy
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.NeuralCoding.SeidelTriangleHolonomy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/NeuralCoding/SeidelTriangleHolonomy.lean by skeleton subtraction
import Mathlib
/-
# Seidel third moment as signed-triangle holonomy

This file connects the third spectral moment of a Seidel matrix with a purely
combinatorial parity statistic on triples of vertices.  Each ordered triple of
distinct vertices contributes `-1` when it spans an odd number of graph edges
and `+1` when it spans an even number.  Thus the matrix trace is exactly the
imbalance between even- and odd-edge ordered triples.

The same product is the holonomy of a signed graph around a triangle.  A vertex
switching multiplies an edge sign by one sign at each endpoint; all vertex signs
cancel around a triangle.  This gives a local, gauge-theoretic explanation of
the invariance of the cubic trace under Seidel switching.
-/

open Matrix BigOperators

namespace SeidelTriangleHolonomy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Seidel matrix of a loopless adjacency relation. -/
def seidel (adj : V → V → Prop) [DecidableRel adj] : Matrix V V ℝ :=
  fun i j => if i = j then 0 else if adj i j then -1 else 1

/-- An odd number of the three cyclic pairs are edges. -/
def OddEdgeTriple (adj : V → V → Prop) (i j k : V) : Prop :=
  (adj i j ∧ ¬ adj j k ∧ ¬ adj k i) ∨
  (¬ adj i j ∧ adj j k ∧ ¬ adj k i) ∨
  (¬ adj i j ∧ ¬ adj j k ∧ adj k i) ∨
  (adj i j ∧ adj j k ∧ adj k i)

instance (adj : V → V → Prop) [DecidableRel adj] (i j k : V) :
    Decidable (OddEdgeTriple adj i j k) := by
  unfold OddEdgeTriple
  infer_instance

/-- The parity weight of an ordered triple: repeated vertices contribute zero;
otherwise odd-edge triples contribute `-1` and even-edge triples `+1`. -/
def parityWeight (adj : V → V → Prop) [DecidableRel adj] (i j k : V) : ℝ :=
  if i = j ∨ j = k ∨ k = i then 0
  else if OddEdgeTriple adj i j k then -1 else 1





/-! ## A concrete three-vertex check -/

/-
On three vertices, the complete graph has cubic Seidel trace `-6`, while
its complement has trace `6`; the parity formula gives the same values.
-/

end SeidelTriangleHolonomy


