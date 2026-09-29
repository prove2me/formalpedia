-- Prove2me | Definitions.Def_Novelty_UniformVCStar
-- name    : Novelty_UniformVCStar
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:25.196768+00:00
-- url     : https://prove2.me/theorems/4472e8b8-4633-402b-856c-6e8b75f96401
-- title:
--   Aether Catalog definitions — Novelty_UniformVCStar
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniformVCStar`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniformVCStar.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A uniform set family of VC dimension at most `d` and size `Mformula n d`

This file realises the construction promised by `LayeredStarFormula.lean`: an
explicit *uniform* set family over `Fin n` whose VC dimension is at most `d` and
whose cardinality is exactly `Mformula n d = C(n, ⌊d/2⌋)`.

* `Shatters F S`           — every subset of `S` is cut out by some member of `F`;
* `VCdimLe F d`            — no shattered set exceeds `d` points;
* `uniformStarFamily n d`  — all `⌊d/2⌋`-element subsets of `Fin n`;
* `uniformStarFamily_uniform`  — it is uniform (every member has `⌊d/2⌋` points);
* `uniformStarFamily_card`     — its size is `Mformula n d`;
* `uniformStarFamily_vcDimLe`  — its VC dimension is at most `d`;
* `exists_uniform_VC_family`   — the packaged existence statement.

The VC bound is sharp at the level of the construction: shattering a set `S`
requires (taking `T = S`) some `⌊d/2⌋`-set containing `S`, forcing
`|S| ≤ ⌊d/2⌋ ≤ d`.
-/

open Finset

namespace Catalog.Novelty.UniformVCStar

variable {n : ℕ}

/-- A set family `F` over `Fin n` **shatters** `S` if every subset `T ⊆ S` is
realized as `s ∩ S` for some member `s ∈ F`. -/
def Shatters (F : Finset (Finset (Fin n))) (S : Finset (Fin n)) : Prop :=
  ∀ T ⊆ S, ∃ s ∈ F, s ∩ S = T

/-- `F` has VC dimension at most `d`: no shattered set has more than `d` points. -/
def VCdimLe (F : Finset (Finset (Fin n))) (d : ℕ) : Prop :=
  ∀ S : Finset (Fin n), Shatters F S → S.card ≤ d

/-- The size of the central uniform layer, `C(n, ⌊d/2⌋)`. -/
def Mformula (n d : ℕ) : ℕ := n.choose (d / 2)

/-- The **uniform layered-star family**: all `⌊d/2⌋`-element subsets of `Fin n`. -/
def uniformStarFamily (n d : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard (d / 2)





end Catalog.Novelty.UniformVCStar


