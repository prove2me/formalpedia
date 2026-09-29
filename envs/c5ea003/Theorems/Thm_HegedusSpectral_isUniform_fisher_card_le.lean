-- Prove2me | Theorems.Thm_HegedusSpectral_isUniform_fisher_card_le
-- name    : HegedusSpectral.isUniform_fisher_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:58:50.63565+00:00
-- url     : https://prove2.me/theorems/28695a0d-d3cd-429f-abcf-1b475dc71957
-- title:
--   Uniform Fisher bound for `Finset` families (catalog-bridged form).
-- statement:
--   **Uniform Fisher bound for `Finset` families (catalog-bridged form).**
--
--   Stated with the `IsUniform` predicate from
--   `Novelty/CrossIntersectingProductBound.lean`: a `k`-uniform family `𝓕` of subsets
--   of `Fin n` in which any two distinct members meet in exactly `λ < k` points has at
--   most `n` members.
--
--   ```lean
--   theorem HegedusSpectral.isUniform_fisher_card_le(𝓕 : Finset (Finset (Fin n))) (k lam : ℕ)
--       (hlam : lam < k)
--       (hU : CrossIntersectingProduct.IsUniform k 𝓕)
--       (hint : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → (A ∩ B).card = lam) : 𝓕.card ≤ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EquiangularFisher.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EquiangularFisher.lean#L71

-- Thm stub generated from Novelty/EquiangularFisher.lean
import Mathlib
import Definitions.Def_Novelty_CrossIntersectingProductBound
import Definitions.Def_Novelty_EquiangularFisher
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

open HegedusSpectral

variable {n : ℕ}

theorem HegedusSpectral.isUniform_fisher_card_le(𝓕 : Finset (Finset (Fin n))) (k lam : ℕ)
    (hlam : lam < k)
    (hU : CrossIntersectingProduct.IsUniform k 𝓕)
    (hint : ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ≠ B → (A ∩ B).card = lam) : 𝓕.card ≤ n := by sorry
