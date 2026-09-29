-- Prove2me | Theorems.Thm_LibraryOfBabel_distributed_catalog_iff
-- name    : LibraryOfBabel.distributed_catalog_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:53:37.067531+00:00
-- url     : https://prove2.me/theorems/cb28db7a-5bce-4c11-a5f9-0147caa33010
-- title:
--   Exact distributed-catalog threshold.
-- statement:
--   **Exact distributed-catalog threshold.** For a nonempty alphabet, a complete
--   distributed catalog spanning `N` volumes exists **iff** `A ^ L ≤ N`.  Each catalog
--   volume can identify exactly one library volume, so the honest threshold is the
--   full Library size `A^L` — not the theme's heuristic `A^L/(L·log₂A)`.
--
--   ```lean
--   theorem LibraryOfBabel.distributed_catalog_iff{A L N : ℕ} (hA : 1 ≤ A) :
--       (∃ c : Fin N → Volume A L, CompleteDistributedCatalog c) ↔ A ^ L ≤ N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LibraryOfBabel/Catalog.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LibraryOfBabel/Catalog.lean#L98

-- Thm stub generated from Cryptography/LibraryOfBabel/Catalog.lean
import Mathlib
import Definitions.Def_Cryptography_KMerAvoidance
import Definitions.Def_Cryptography_LibraryOfBabel_Basic
import Definitions.Def_Cryptography_LibraryOfBabel_Catalog
/-
# The Library of Babel: Catalogs, the Diagonal Argument, and Distributed Guides

Borges' deepest question: can the Library contain its own complete catalog?

We model a **complete catalog** of the Library as a *subset* of volumes (for each
volume, whether it is listed), i.e. an element of `Set (Volume A L)`.  A single
volume can encode at most one message, so a "self-catalog" would be a map from
volumes to catalogs; the diagonal argument shows no such map is onto.  A
**distributed catalog** spreads the listing across `N` volumes, and we pin down
exactly how large `N` must be.

## Main Results (this file)

1. **No single-volume complete catalog** (`no_complete_self_catalog`): there is no
   surjection `Volume A L → Set (Volume A L)`.  Equivalently (`card_catalogs_gt`),
   the number of possible catalogs `2 ^ (A ^ L)` strictly exceeds the number of
   volumes `A ^ L`, so no volume can be assigned a distinct catalog.  This is the
   rigorous diagonal obstruction.

2. **Exact distributed-catalog threshold** (`distributed_catalog_iff`): a
   distributed catalog `c : Fin N → Volume A L` that lists *every* volume
   (surjective) exists **iff** `A ^ L ≤ N`.  This corrects the theme's heuristic
   threshold `N > A^L / (L·log₂A)`: since each catalog volume can *identify* only
   one library volume, the true threshold is `N ≥ A^L`, not `A^L / (L log₂ A)`.

3. **de Bruijn catalog capacity** (`catalog_codes_le`, `catalog_forces_collision`):
   bridging to `KMerAvoidance`, a single index volume of length `L` can exhibit
   at most `A^k` distinct length-`k` reference codes (`= |mini-Library of length
   k|`), and once `L ≥ A^k + k` a code *must* repeat — so the shortest lossless
   single-volume catalog of all `A^k` codes has length `A^k + k - 1`, exactly the
   length of a de Bruijn sequence `B(A,k)`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): (a) the Library cannot hold its own complete catalog;
(b) a distributed catalog needs `N > A^L/(L log₂ A)` volumes; (c) a de Bruijn
sequence yields an optimal single-volume "mini-catalog".

Experiment (Experimenter): mini-Library `A=4, L=16` has `4^16 = 4294967296`
volumes.  A single catalog volume is one string; it can *point at* one volume, so
listing all needs `4^16` catalog volumes.  The heuristic `A^L/(L log₂ A) =
4^16/(16·2) = 4^16/32 ≈ 1.3e8` is far too small — off by a factor `L log₂ A = 32`.
For de Bruijn: `B(4,2)` has length `4^2 = 16`, wraps to cover all `16` length-2
codes; linearised length `4^2 + 2 - 1 = 17`.

Analysis (Analyst): the info-theoretic heuristic silently assumes a catalog
volume can be *subdivided* into `L log₂ A` independent pointer bits.  But a
catalog entry that must *name a whole volume* consumes a whole volume's worth of
symbols; the honest counting threshold is therefore `A^L`, proved by a bijection
`Volume ≃ Fin (A^L)` plus a Fin-surjection.  The diagonal fact is finite Cantor:
`2^(A^L) > A^L`.

Critique (Critic): is `distributed_catalog_iff` vacuous?  No — both directions are
load-bearing: `←` builds an explicit surjection from `A^L ≤ N`; `→` uses
`Fintype.card_le_of_surjective`.  The `A ≥ 1` hypothesis is necessary: with `A=0`
and `L>0` the Library is empty and the statement degenerates.

Synthesis (PI): the three results together say meaning in the Library is
*locatable but not self-locating*: a guide exists, but only as a distributed
structure of full size, never as a single self-referential volume.
-/

open Finset Fintype Function LibraryOfBabel

open LibraryOfBabel

/-! ## The diagonal argument: no single-volume complete catalog -/



/-! ## The distributed catalog threshold -/

theorem LibraryOfBabel.distributed_catalog_iff{A L N : ℕ} (hA : 1 ≤ A) :
    (∃ c : Fin N → Volume A L, CompleteDistributedCatalog c) ↔ A ^ L ≤ N := by sorry
