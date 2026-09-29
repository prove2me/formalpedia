-- Prove2me | Definitions.Def_Bridges_RuckerInfinityHierarchy
-- name    : Bridges_RuckerInfinityHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:38:59.86318+00:00
-- url     : https://prove2.me/theorems/dbffe562-3b06-4ade-bc57-8635d9d461eb
-- title:
--   Aether Catalog definitions — Bridges_RuckerInfinityHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.RuckerInfinityHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/RuckerInfinityHierarchy.lean by skeleton subtraction
import Mathlib

/-!
# Rucker: Infinity and the Mind — Cantor's Hierarchy of Infinities

This file formalizes, in Lean 4 / Mathlib, several load-bearing facts about the
Cantorian hierarchy of infinite cardinals, in the spirit of Rudy Rucker's
*Infinity and the Mind* and its slogan that "infinity is a place you can visit".

We work entirely inside ZFC as available in Mathlib (which uses classical logic
and choice). The results are grouped into themes:

* **The Cantor tower** — an explicit, strictly increasing infinite tower of
  cardinals `ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ⋯` (a truncated *beth* sequence). This is
  the concrete sense in which one can "keep visiting larger infinities".
* **No largest infinity** — the cardinals form a proper class: there is no
  cardinal above all cardinals, and every power set is strictly larger than its
  base (Cantor's theorem).
* **Hartogs' theorem** — for *every* type there is a (well-orderable) ordinal
  whose cardinality strictly exceeds it. This holds with no appeal to the power
  set of `α`.
* **`ℵ₁` and the Continuum Hypothesis** — `ℵ₀ < ℵ₁ ≤ 𝔠`, and CH is *exactly*
  the remaining inequality `𝔠 ≤ ℵ₁`.
* **König's theorem in action** — the continuum has uncountable cofinality, and
  as a *disproof* of a naive guess, `𝔠 ≠ ℵ_ω`.
* **Large-cardinal flavour** — `ℵ₀` is regular and a strong limit; it fails to
  be inaccessible *only* because inaccessibility demands uncountability. In this
  precise sense `ℵ₀` is "the first unreachable place".

All theorems are proved in ZFC; the independence of CH itself is discussed in
`FUTURE_DIRECTIONS.md`.
-/

open Cardinal Ordinal

universe u

namespace RuckerInfinity

/-! ## 1. The Cantor tower: an explicit strictly increasing tower of infinities -/

/-- A truncated *beth* sequence: `cantorTower 0 = ℵ₀` and
`cantorTower (n+1) = 2 ^ cantorTower n`.  This realizes Rucker's picture of
successively "visiting" larger infinities `ℵ₀ < 2^ℵ₀ < 2^(2^ℵ₀) < ⋯`. -/
noncomputable def cantorTower : ℕ → Cardinal.{u}
  | 0 => Cardinal.aleph0
  | (n + 1) => 2 ^ (cantorTower n)






/-! ## 2. No largest infinity: the cardinals form a proper class -/




/-! ## 3. Hartogs' theorem: a well-orderable bound above any type -/


/-! ## 4. `ℵ₁`, the first uncountable cardinal, and the Continuum Hypothesis -/



/-- The **Continuum Hypothesis**: `ℵ₁ = 𝔠` (stated for the base universe, where
the continuum `𝔠 = #ℝ` lives). -/
def ContinuumHypothesis : Prop := Cardinal.aleph.{0} 1 = Cardinal.continuum.{0}



/-! ## 5. König's theorem: cofinality of the continuum, and `𝔠 ≠ ℵ_ω` -/




/-! ## 6. Large-cardinal flavour: `ℵ₀` as "the first unreachable place" -/




end RuckerInfinity


