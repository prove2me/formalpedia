-- Prove2me | Theorems.Thm_BoltzmannBridge_Filtration_stability_two_sided
-- name    : BoltzmannBridge.Filtration.stability_two_sided
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:23:21.072278+00:00
-- url     : https://prove2.me/theorems/0ab9671e-a88f-460c-a826-eadbc8fa440c
-- title:
--   Two-sided stability.
-- statement:
--   **Two-sided stability.**  Uniform closeness of the weights (`|F − G| ≤ δ`)
--   yields a symmetric `δ`-interleaving of the sublevel families.
--
--   ```lean
--   theorem BoltzmannBridge.Filtration.stability_two_sided(F G : Filtration α) {δ : ℝ}
--       (h : ∀ σ : Finset α, |F.weight σ - G.weight σ| ≤ δ) (t : ℝ) :
--       F.sublevelFaces t ⊆ G.sublevelFaces (t + δ) ∧
--       G.sublevelFaces t ⊆ F.sublevelFaces (t + δ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BoltzmannBridge/PersistenceStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BoltzmannBridge/PersistenceStability.lean#L105

-- Thm stub generated from Applications/BoltzmannBridge/PersistenceStability.lean
import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
/-
# The Boltzmann Bridge III — Stability and Functoriality of Sublevel Filtrations

This file extends the catalog's higher-dimensional persistence machinery
(`Applications.BoltzmannBridge.HigherPersistence`, which builds
`ASC` abstract simplicial complexes, the sublevel `Filtration` calculus, the
Vietoris–Rips filtration, and `euler_char_full_simplex`) with the two structural
pillars that make persistent homology a *robust* invariant of data:

* **Functoriality.**  The containment relation `ASC.Sub` between complexes is a
  preorder (reflexive and transitive), so the sublevel complexes of a fixed
  filtration assemble into a one-parameter diagram of inclusions — the
  combinatorial skeleton of a *persistence module*.

* **Stability / interleaving.**  If two filtrations have uniformly close weight
  functions (`G.weight σ ≤ F.weight σ + δ`), then their sublevel families are
  `δ`-interleaved: `F.sublevelFaces t ⊆ G.sublevelFaces (t + δ)`.  The
  interleaving bounds compose additively (`stability_compose`), which is the
  triangle inequality underlying the *interleaving / bottleneck distance*.  This
  is the algebraic core of the Cohen-Steiner–Edelsbrunner–Harer stability
  theorem, here proved at the level of the filtration itself.

Lattice compatibility (`sublevelFaces_min`, `VRfaces_min`) records that sublevel
sets turn the `min` of scales into intersection of complexes.

## Main results

* `ASC.Sub_refl`, `ASC.Sub_trans` — `ASC.Sub` is a preorder (persistence functoriality)
* `Filtration.sublevelComplex_sub` — connecting maps of the persistence module
* `Filtration.sublevelFaces_min` — sublevel of a `min` is the intersection
* `Filtration.stability_interleaving` — δ-closeness ⇒ δ-interleaving of sublevels
* `Filtration.stability_compose` — interleavings compose additively (triangle ineq.)
* `Filtration.stability_two_sided` — symmetric closeness ⇒ two-sided interleaving
* `VRfaces_min` — Vietoris–Rips turns `min` of scales into intersection
-/

open Finset BigOperators

open BoltzmannBridge

open ASC

variable {α : Type*}

-- !-- Reflexivity is `subset_refl` on the face sets. -- !--

-- !-- Transitivity is transitivity of `⊆` on face sets; chaining the inclusions
-- !-- realizes the composition of the persistence-module connecting maps. -- !--


open Filtration

variable {α : Type*}

-- !-- The face sets of the two sublevel complexes are literally the sublevel sets,
-- !-- so the containment is exactly `sublevel_mono`. -- !--

-- !-- `weight σ ≤ min t₁ t₂ ↔ weight σ ≤ t₁ ∧ weight σ ≤ t₂` (le_min_iff). -- !--

-- !-- From `F.weight σ ≤ t` and `G.weight σ ≤ F.weight σ + δ` we get
-- !-- `G.weight σ ≤ t + δ` by transitivity and monotonicity of `+`. -- !--

-- !-- Apply `stability_interleaving F G` to land in `G` at `t+δ`, then
-- !-- `stability_interleaving G H` to land in `H` at `(t+δ)+δ'`. -- !--

-- !-- Each direction is an instance of `stability_interleaving` after rearranging
-- !-- the symmetric bound `|F.weight σ - G.weight σ| ≤ δ` via `abs_le`. -- !--

theorem BoltzmannBridge.Filtration.stability_two_sided(F G : Filtration α) {δ : ℝ}
    (h : ∀ σ : Finset α, |F.weight σ - G.weight σ| ≤ δ) (t : ℝ) :
    F.sublevelFaces t ⊆ G.sublevelFaces (t + δ) ∧
    G.sublevelFaces t ⊆ F.sublevelFaces (t + δ) := by sorry
