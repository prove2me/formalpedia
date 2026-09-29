-- Prove2me | Definitions.Def_Novelty_EquiangularFisher
-- name    : Novelty_EquiangularFisher
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:22:10.531021+00:00
-- url     : https://prove2.me/theorems/a1602e61-8d25-4d19-9b9b-3e88e76007d9
-- title:
--   Aether Catalog definitions — Novelty_EquiangularFisher
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EquiangularFisher`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EquiangularFisher.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_CrossIntersectingProductBound
import Definitions.Def_Novelty_SpectralBound
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A Fisher / Frankl–Wilson type bound via the spectral Gram constraint

Building on the abstract spectral bound of `SpectralBound.lean`, this file proves a
genuine **extremal set-system** theorem by the linear-algebra (eigenvalue) method:

> If a family of `m` subsets of an `n`-element ground set is **`k`-uniform**
> (each set has size `k`) and any two *distinct* members meet in exactly `λ`
> points with `λ < k`, then `m ≤ n`.

The proof attaches to each set its real **incidence vector** in `ℝ^n`; the Gram
matrix of these vectors is the *intersection matrix* with diagonal `k` and
off-diagonal `λ`, i.e. exactly the constant-pattern matrix `(k − λ)·I + λ·J`.
Its positive definiteness (Hegedűs' eigenvalue condition) forces linear
independence, hence the bound `m ≤ n`.

This **bridges two catalog domains**: it reuses the combinatorial vocabulary of
`Novelty/CrossIntersectingProductBound.lean` (the `IsUniform` predicate for
families of finite sets) and the spectral machinery of `SpectralBound.lean`.
-/

open Matrix

namespace HegedusSpectral

variable {n : ℕ}

/-- The real **incidence vector** of a finite set `A ⊆ Fin n` inside `ℝ^n`:
the `0/1` indicator of membership. -/
noncomputable def incidence (A : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun t => if t ∈ A then (1 : ℝ) else 0)





/-! ## A concrete verified instance (falsifiability through construction)

The family of all `n` singletons `{0}, …, {n-1}` in `Fin n` is `1`-uniform with
pairwise intersection `0 = λ < 1 = k`, achieving `m = n`.  This witnesses that the
bound `m ≤ n` is attained and that the eigenvalue hypothesis is satisfiable. -/

/-- The `n` singleton subsets of `Fin n`, indexed by `Fin n`. -/
def singletonFamily (n : ℕ) : Fin n → Finset (Fin n) := fun i => {i}


end HegedusSpectral

/-
-- !-- Lab Notes -- !--

Category (Menu Balance v19a): CROSS-DOMAIN BRIDGE
  This file is the explicit bridge: it imports the spectral engine
  (`SpectralBound.lean`) AND the combinatorial vocabulary of the catalog file
  `Novelty/CrossIntersectingProductBound.lean` (the `IsUniform` predicate), and
  derives a Fisher / Frankl–Wilson type extremal-set bound from the eigenvalue
  inequality.

Hypothesis (Hypothesizer):
  H1. The inner product of two 0/1 incidence vectors equals the size of the
      intersection of the underlying sets — the combinatorics ↔ algebra
      dictionary.
  H2. A `k`-uniform family with constant pairwise intersection `λ < k` has its
      intersection matrix equal to the constant-pattern Gram matrix, hence is
      bounded by `n`.
  H3 (bold). The bound holds for unindexed `Finset`-families verbatim once they
      are enumerated, so the catalog `IsUniform` predicate plugs in directly.

Experiment (Experimenter):
  * `incidence_inner` : confirmed H1 by reducing `⟪𝟙_A, 𝟙_B⟫` to a sum of
    indicator products and recognising `A ∩ B`.
  * `indexed_fisher_card_le` : confirmed H2 by feeding the inner-product values
    into `constGram_card_le`; the casts `(lam:ℝ) < (k:ℝ)` come from `lam < k`.
  * `isUniform_fisher_card_le` : confirmed H3 by enumerating `𝓕` via
    `Finset.equivFin` and transporting `IsUniform`/intersection hypotheses.
  * `singletonFamily_fisher` : a verified tight instance (`k=1, λ=0, m=n`).

Analysis (Analyst):
  - The key reduction is purely the dictionary lemma `incidence_inner`; once the
    Gram matrix is identified, all combinatorial content is spectral.
  - Failure mode encountered: an early attempt used `WithLp.equiv_symm_pi_apply`
    (nonexistent here); the working route is that `(·).ofLp` of the symm-equiv is
    definitionally the indicator, so the sum simplifies directly.

Critique (Critic):
  - `isUniform_fisher_card_le` genuinely USES the attached catalog
    (`CrossIntersectingProduct.IsUniform`), satisfying the catalog-usage rule.
  - The hypothesis `λ < k` is necessary; its necessity is demonstrated by an
    explicit construction in `FalsifiabilityWitness.lean`.
  - No result is vacuous: `singletonFamily_fisher` is a non-empty witness, and
    the main bounds use `constGram_card_le` (a non-trivial inequality).

Synthesis (PI):
  Classical uniform Fisher-type bounds are a corollary of a single Gram-matrix
  eigenvalue inequality; the catalog's set-family language slots in unchanged.
-/


