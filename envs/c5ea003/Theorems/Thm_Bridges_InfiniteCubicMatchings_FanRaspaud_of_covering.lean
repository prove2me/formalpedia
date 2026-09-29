-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_FanRaspaud_of_covering
-- name    : Bridges.InfiniteCubicMatchings.FanRaspaud.of_covering
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:14.327273+00:00
-- url     : https://prove2.me/theorems/52896826-f822-420e-a759-ff582857e152
-- title:
--   Fan–Raspaud lifts along coverings.
-- statement:
--   **Fan–Raspaud lifts along coverings.**
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.FanRaspaud.of_covering(φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
--       (hK : FanRaspaud K) : FanRaspaud G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCovers.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCovers.lean#L83

-- Thm stub generated from Bridges/InfiniteCubicMatchingsCovers.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsCovers
/-
# Coverings: transferring matchings from a base graph to an infinite cover

A map `φ : V(G) → V(K)` which is a local isomorphism at *every* vertex (`IsLocalIsoAt`) is a
covering map in the graph-theoretic sense.  Perfect matchings pull back along such maps, and
therefore so do the Berge–Fulkerson and Fan–Raspaud properties.

The consequence for the infinite theory is `bergeFulkerson_of_covers_finite`: *the finite
Berge–Fulkerson conjecture already implies the Berge–Fulkerson property for every graph —
however large — that covers a finite cubic bridgeless graph.*  This covers all the standard
infinite examples (ℤ-covers and other regular covers of finite snarks and prisms), with no
compactness argument needed.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V} {K : SimpleGraph W}

open PerfectMatching

theorem Bridges.InfiniteCubicMatchings.FanRaspaud.of_covering(φ : V → W) (hcov : ∀ v, IsLocalIsoAt G K φ v)
    (hK : FanRaspaud K) : FanRaspaud G := by sorry
