-- Prove2me | solution 1 for BoltzmannBridge.mem_VRfaces
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:15:05.108831+00:00
-- url     : https://prove2.me/submissions/0fcc2445-9130-4391-bd91-0a50851ee7d4

-- Sol generated from Applications/BoltzmannBridge/HigherPersistence.lean
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



-- !-- Every pairwise distance `≤ ε₁ ≤ ε₂`, so a face survives the larger scale. -- !--

-- !-- A singleton's only pair is `(x, x)` with `dist x x = 0 ≤ ε`. -- !--

-- !-- `diamWeight σ ≤ ε` unfolds, via `Finset.sup'_le_iff`, to: `0 ≤ ε` and every
-- !-- pairwise distance `≤ ε` — exactly the VR membership condition. -- !--


/-! ## Euler characteristic of the full simplex -/

-- !-- From `∑_{m=0}^{n} (-1)^m C(n,m) = 0` (the alternating binomial identity for
-- !-- `n ≥ 1`), split off the `m=0` term and reindex to get the value `1`. -- !--


open BoltzmannBridge in
@[simp] theorem solution(ε : ℝ) (σ : Finset α) :
    σ ∈ VRfaces ε ↔ ∀ x ∈ σ, ∀ y ∈ σ, dist x y ≤ ε := Iff.rfl
