-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_FixedPointsPoisson
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T15:13:24.84984+00:00
-- url     : https://prove2.me/theorems/aa278ce0-c9b6-4b33-80a6-b6be9c3d5c8a
-- title:
--   Fixed-point counts, finite averages and incidence types
-- statement:
--   fixedPointCount is the cardinality of the fixed-vertex subtype of a permutation of Fin n. Uniform expectations divide finite sums over all permutations by n!. Finite incidence types and complement-permutation equivalences count ordered fixed-point embeddings; the exact favorable count and PMF use the derangement enumeration.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/FixedPointsPoisson.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Fixed points in a random permutation

This file records the discrete Poisson(1) limit for fixed points of a uniform
random permutation at the level currently most directly supported by Mathlib:

* the exact factorial-moment identity
  `E[(F_n)_k] = 1` for `k <= n`;
* the pointwise probability mass limit
  `P(F_n = j) -> exp(-1) / j!`.

The probability mass is expressed by the genuine derangement count
`choose n j * D_{n-j} / n!`.
-/

noncomputable section

open Filter
open scoped Topology NNReal

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws
namespace FixedPointsPoissonNS

/-- The number of fixed points of a permutation of `Fin n`. -/
def fixedPointCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  Fintype.card {i : Fin n // σ i = i}

/-- Uniform expectation over permutations of `Fin n`, as a finite average. -/
def uniformPermExpectation (n : ℕ) (X : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin n), X σ) / n.factorial

/-- Embeddings whose image is pointwise fixed by a given permutation. -/
def FixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) : Type :=
  {e : Fin k ↪ Fin n // ∀ i, σ (e i) = e i}

/-- Permutations that pointwise fix the image of a given embedding. -/
def PermFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) : Type :=
  {σ : Equiv.Perm (Fin n) // ∀ i, σ (e i) = e i}

instance instFintypeFixedEmbeddingsOfPerm (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    Fintype (FixedEmbeddingsOfPerm n k σ) := by
  classical
  unfold FixedEmbeddingsOfPerm
  infer_instance

instance instFintypePermFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Fintype (PermFixingEmbedding n k e) := by
  classical
  unfold PermFixingEmbedding
  infer_instance

/-- Count the same incidence relation first by permutations. -/
abbrev FixedEmbeddingByPerm (n k : ℕ) : Type :=
  Σ σ : Equiv.Perm (Fin n), FixedEmbeddingsOfPerm n k σ

/-- Count the same incidence relation first by ordered fixed-point choices. -/
abbrev FixedEmbeddingByEmbedding (n k : ℕ) : Type :=
  Σ e : Fin k ↪ Fin n, PermFixingEmbedding n k e

/-- A fixed ordered `k`-tuple in the fixed-point set is the same as an embedding
into the fixed-point subtype. -/
def fixedEmbeddingsOfPermEquiv (n k : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Fin k ↪ {i : Fin n // σ i = i}) ≃ FixedEmbeddingsOfPerm n k σ where
  toFun f :=
    ⟨f.trans (Function.Embedding.subtype _), fun i => (f i).2⟩
  invFun e :=
    { toFun := fun i => ⟨e.1 i, e.2 i⟩
      inj' := by
        intro a b h
        exact e.1.injective (Subtype.ext_iff.mp h) }
  left_inv f := by
    ext i
    rfl
  right_inv e := by
    cases e with
    | mk e h =>
      rfl

/-- A permutation of the complement of `range e` is the same as a permutation of
`Fin n` fixing `range e` pointwise. -/
def complementPermEquivFixingEmbedding (n k : ℕ) (e : Fin k ↪ Fin n) :
    Equiv.Perm {x : Fin n // x ∉ Set.range e} ≃ PermFixingEmbedding n k e :=
  (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Fin n => x ∉ Set.range e)).trans
    { toFun := fun σ =>
        ⟨σ.1, by
          intro i
          exact σ.2 (e i) (by
            intro h
            exact h ⟨i, rfl⟩)⟩
      invFun := fun σ =>
        ⟨σ.1, by
          intro a ha
          have hmem : a ∈ Set.range e := by
            by_contra h
            exact ha h
          rcases hmem with ⟨i, rfl⟩
          exact σ.2 i⟩
      left_inv := by
        rintro ⟨σ, hσ⟩
        rfl
      right_inv := by
        rintro ⟨σ, hσ⟩
        rfl }

/-- Swap the two ways of presenting the fixed-point incidence relation. -/
def fixedEmbeddingByPermEquivByEmbedding (n k : ℕ) :
    FixedEmbeddingByPerm n k ≃ FixedEmbeddingByEmbedding n k where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  left_inv := by
    rintro ⟨σ, e, h⟩
    rfl
  right_inv := by
    rintro ⟨e, σ, h⟩
    rfl

/-- The derangement-count expression for the fixed-point probability mass. -/
def fixedPointFavourableCount (n j : ℕ) : ℕ :=
  n.choose j * numDerangements (n - j)

/-- Probability mass `P(F_n = j)` expressed by choosing the fixed points and
deranging the complement. For `j > n` this is zero because `n.choose j = 0`. -/
def fixedPointPMF (n j : ℕ) : ℝ :=
  (fixedPointFavourableCount n j : ℝ) / n.factorial

end FixedPointsPoissonNS
end LimitLaws
end Ch9
end AnalyticCombinatorics


