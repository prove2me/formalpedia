-- Prove2me | Theorems.Thm_chain_cover_card_ge_middle
-- name    : chain_cover_card_ge_middle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T15:01:05.056185+00:00
-- url     : https://prove2.me/theorems/0dc9fcbe-7eaf-402a-a11b-fdce852e839d
-- title:
--   Chain-cover lower bound for the Boolean lattice.
-- statement:
--   **Chain-cover lower bound for the Boolean lattice.**  If `𝒞` is a family of
--   chains (each `C ∈ 𝒞` is a chain of subsets under `⊆`) whose union covers every
--   subset of `Fin n`, then `𝒞` contains at least `n.choose (n / 2)` chains.
--
--   ```lean
--   theorem chain_cover_card_ge_middle    {𝒞 : Finset (Finset (Finset (Fin n)))}
--       (h_chain : ∀ C ∈ 𝒞, IsChain (· ⊆ ·) (C : Set (Finset (Fin n))))
--       (h_cover : ∀ s : Finset (Fin n), ∃ C ∈ 𝒞, s ∈ C) :
--       𝒞.card ≥ n.choose (n / 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/SpernerChainCover.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/SpernerChainCover.lean#L64

-- Thm stub generated from Logic/PosetTheory/SpernerChainCover.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_SpernerChainCover
/-
# A Chain-Cover Lower Bound for the Boolean Lattice

This file proves a lower bound on the number of chains needed to cover the
Boolean lattice `Finset (Fin n)`: any family of chains whose union covers every
subset of `Fin n` must contain at least `n.choose (n / 2)` chains.

The argument is the "easy half" of Dilworth-type reasoning specialised to the
Boolean lattice: the middle layer (all subsets of size `n / 2`) is an antichain
of size `n.choose (n / 2)`, and any chain meets an antichain in at most one
element, so at least `n.choose (n / 2)` chains are required.

## Note on the statement

The requested statement declared `𝒞 : Finset (Finset (Fin n))`.  That type is not
consistent with the hypotheses: `h_chain` asks each `C ∈ 𝒞` to be a *chain* of
subsets, i.e. `C : Finset (Finset (Fin n))` (coerced to `Set (Finset (Fin n))`),
and `h_cover` asks `s : Finset (Fin n)` to be a *member* of some `C ∈ 𝒞`.  Both
force each element of `𝒞` to be a `Finset (Finset (Fin n))`, hence
`𝒞 : Finset (Finset (Finset (Fin n)))`.  We use this corrected, type-correct
type for `𝒞`.
-/

open Finset

variable {n : ℕ}

theorem chain_cover_card_ge_middle    {𝒞 : Finset (Finset (Finset (Fin n)))}
    (h_chain : ∀ C ∈ 𝒞, IsChain (· ⊆ ·) (C : Set (Finset (Fin n))))
    (h_cover : ∀ s : Finset (Fin n), ∃ C ∈ 𝒞, s ∈ C) :
    𝒞.card ≥ n.choose (n / 2) := by sorry
