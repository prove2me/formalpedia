-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_ChoraleRigidity
-- name    : Tropical_AbstractAlgebra_ChoraleRigidity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:28:49.897231+00:00
-- url     : https://prove2.me/theorems/eca8762c-a6e3-448a-84d5-0be21348c4cc
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_ChoraleRigidity
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.ChoraleRigidity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/ChoraleRigidity.lean by skeleton subtraction
import Mathlib

/-!
# Four-Voice Chorale Cost and Zero-Cost Rigidity

This module formalizes:

1. **Chorale cost functional**: A four-voice cost assembled from pairwise
   voice-interaction terms and unary spacing/register penalties.

2. **Forward zero-cost theorem** (`choraleCost_eq_zero_of_pairwise_zero`):
   If every pair cost and every spacing penalty vanishes, the total cost is zero.

3. **Converse rigidity theorem** (`pairwise_zero_of_choraleCost_eq_zero`):
   If the total cost is zero and every summand is nonneg, then every pairwise
   interaction cost and every spacing penalty vanishes individually.

This is a formal **local-to-global optimality certificate** for polyphonic
writing: it turns a global optimum certificate into six local certificates
plus four unary certificates.
-/

open Finset BigOperators

noncomputable section

/-- A melody of length `n` is a sequence of integer pitches. -/
def Melody' (n : ℕ) := Fin n → ℤ

/-- A chorale is a 4-tuple of melodies, one for each voice (S, A, T, B). -/
def Chorale (n : ℕ) := Fin 4 → Melody' n

/-- The six unordered voice pairs `(i,j)` with `i < j`. -/
def voicePairs : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.1 < p.2)

/-- The four-voice chorale cost: sum of pairwise costs over the six voice pairs,
    plus unary spacing penalties for each voice. -/
def choraleCost {n : ℕ} (pairCost : Melody' n → Melody' n → ℝ)
    (spacingPenalty : Fin 4 → Melody' n → ℝ) (C : Chorale n) : ℝ :=
  (∑ p ∈ voicePairs, pairCost (C p.1) (C p.2)) +
  ∑ i : Fin 4, spacingPenalty i (C i)

/-
There are exactly 6 voice pairs.
-/


/-! ## Forward direction: local zeros imply global zero -/

/-
**Forward zero-cost theorem**: If every pairwise cost vanishes on each of the
    six voice pairs and every spacing penalty vanishes, the total chorale cost is zero.
-/

/-! ## Converse rigidity: global zero implies every summand vanishes -/

/-
**Converse rigidity theorem**: If the total chorale cost is zero and every
    summand (pairwise cost and spacing penalty) is nonnegative, then each
    pairwise cost and each spacing penalty vanishes individually.

    This is the structural decomposition theorem: a global optimum certificate
    decomposes into six local pair certificates plus four unary certificates.
-/

/-! ## Generalized nonnegative-sum rigidity -/

/-
**General nonneg-sum lemma**: If a finite sum of nonneg terms is zero,
    each term is zero. This is the key algebraic ingredient.
-/

/-
**Chorale cost is nonneg** when all summands are nonneg.
-/

end


