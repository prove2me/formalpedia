-- Prove2me | Theorems.Thm_BoltzmannBridge_mem_VRfaces
-- name    : BoltzmannBridge.mem_VRfaces
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:25:48.901734+00:00
-- url     : https://prove2.me/theorems/c4b81252-2a75-4c9c-b4a8-77061682ac29
-- title:
--   A simplex is a VR face at scale `ε` iff every pairwise distance is `≤ ε`.
-- statement:
--   **A simplex is a VR face at scale `ε` iff every pairwise distance is `≤ ε`.**
--   Recorded for use as a simp lemma.
--
--   ```lean
--   theorem BoltzmannBridge.mem_VRfaces(ε : ℝ) (σ : Finset α) :
--       σ ∈ VRfaces ε ↔ ∀ x ∈ σ, ∀ y ∈ σ, dist x y ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BoltzmannBridge/HigherPersistence.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BoltzmannBridge/HigherPersistence.lean#L135

-- Thm stub generated from Applications/BoltzmannBridge/HigherPersistence.lean
import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
/-
# The Boltzmann Bridge II — Higher-Dimensional Persistent Homology on Simplicial Complexes

This file extends the catalog's 0-dimensional persistence machinery (cf.
`Catalog/Applications/PoincareData/SimplicialComplex.lean`, which formalizes
`AbstractSimplicialComplex`, the Vietoris–Rips construction, and `vr_mono`) to a
general **filtration calculus** on abstract simplicial complexes, suitable for
persistent homology in arbitrary dimension.

The core idea of persistent homology is that a finite metric/weighted data set
gives rise to a one-parameter *nested family* of simplicial complexes (a
filtration), and the topological features that persist across a wide range of
the parameter encode the true shape of the data.  Here we develop the abstract
backbone of that theory:

* a **sublevel-set filtration** attached to any monotone weight function on
  simplices, together with the proof that each sublevel set is a genuine
  abstract simplicial complex and that the family is nested (monotone);
* the **Vietoris–Rips filtration** as the canonical example, recovered as the
  sublevel filtration of the *diameter* weight, with an explicit
  characterization of the *birth time* of a simplex (the persistence-theoretic
  heart of the construction);
* the **Euler characteristic of the full simplex**, proved via the alternating
  binomial identity — the simplest nonzero higher-dimensional invariant, and the
  combinatorial shadow of the contractibility of a simplex.

## Main results

* `Filtration.sublevelComplex` — sublevel set of a monotone weight is an ASC
* `Filtration.sublevel_mono` — the sublevel family is nested in the parameter
* `vr_mem_iff_diam_le` — VR complex = sublevel set of the diameter weight
* `vr_mono` — the Vietoris–Rips filtration is nested in the scale
* `euler_char_full_simplex` — Euler characteristic of the full (n−1)-simplex is 1
-/

open Finset BigOperators

open BoltzmannBridge

/-! ## Abstract simplicial complexes -/


open ASC

variable {α : Type*}



/-! ## Sublevel-set filtrations from a monotone weight -/


open Filtration

variable {α : Type*}



-- !-- The empty face is born by `t ≥ 0` and `weight ∅ ≤ 0`; downward closure is
-- !-- immediate from `weight_mono`: a subface has no larger weight. -- !--

-- !-- A simplex of weight `≤ t₁ ≤ t₂` still has weight `≤ t₂`; pure transitivity. -- !--


/-! ## The Vietoris–Rips filtration -/


variable {α : Type*} [PseudoMetricSpace α]


-- !-- Empty product gives `sup' {0} = 0`; monotonicity holds since `σ ⊆ τ` makes
-- !-- every pairwise distance of `σ` one of the distances summed over `τ`. -- !--


@[simp]

theorem BoltzmannBridge.mem_VRfaces(ε : ℝ) (σ : Finset α) :
    σ ∈ VRfaces ε ↔ ∀ x ∈ σ, ∀ y ∈ σ, dist x y ≤ ε := by sorry
