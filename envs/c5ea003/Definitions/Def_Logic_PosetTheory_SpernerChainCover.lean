-- Prove2me | Definitions.Def_Logic_PosetTheory_SpernerChainCover
-- name    : Logic_PosetTheory_SpernerChainCover
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:00:23.90039+00:00
-- url     : https://prove2.me/theorems/8f8c4650-c1dc-444b-a10e-f127cebb4f63
-- title:
--   Aether Catalog definitions — Logic_PosetTheory_SpernerChainCover
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PosetTheory.SpernerChainCover`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PosetTheory/SpernerChainCover.lean by skeleton subtraction
import Mathlib
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

/-- The middle layer of the Boolean lattice on `Fin n`: all subsets of
cardinality `n / 2`. -/
def middleLayer (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun s => s.card = n / 2)


