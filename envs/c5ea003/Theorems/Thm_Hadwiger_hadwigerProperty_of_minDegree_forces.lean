-- Prove2me | Theorems.Thm_Hadwiger_hadwigerProperty_of_minDegree_forces
-- name    : Hadwiger.hadwigerProperty_of_minDegree_forces
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:00:40.957467+00:00
-- url     : https://prove2.me/theorems/f396b71d-4b13-4471-b35f-acb2e2d52e6e
-- title:
--   Minimum degree reduction.
-- statement:
--   **Minimum degree reduction.**  If every finite graph of minimum degree at
--   least `k` has a `K_{k+1}` minor, then Hadwiger's conjecture holds for `k`.
--
--   This is one-directional on purpose: the hypothesis is strictly stronger than
--   Hadwiger's conjecture for large `k`, but it is the classical route for `k ≤ 3`.
--
--   ```lean
--   theorem Hadwiger.hadwigerProperty_of_minDegree_forces    (H : ∀ (W : Type) [Finite W] [Nonempty W] (K : SimpleGraph W),
--           (∀ w : W, k ≤ Nat.card (K.neighborSet w)) → CompleteMinor (k + 1) K) :
--       HadwigerProperty k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerCritical.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerCritical.lean#L185

-- Thm stub generated from Probability/HadwigerCritical.lean
import Mathlib
import Definitions.Def_Probability_HadwigerCritical
import Definitions.Def_Probability_HadwigerK3
import Definitions.Def_Probability_HadwigerSmallCases
/-
  # Colour-critical subgraphs and the minimum-degree reduction for Hadwiger's conjecture

  This file closes the first structural step of Conjecture 1 of `FUTURE_DIRECTIONS.md`
  ("Dirac's shape"): it reduces Hadwiger's conjecture for a parameter `k` to the
  *minimum-degree* statement

      every finite graph of minimum degree at least `k` has a `K_{k+1}` minor.

  The reduction proceeds through a colour-critical subgraph:

  1. `ColorableOn` — proper `k`-colourability of a vertex subset;
  2. `exists_critical_subset` — every graph that is not `k`-colourable contains a
     *vertex-minimal* non-`k`-colourable subset;
  3. `exists_subset_minDegree_of_not_colorable` — in that minimal subset **every**
     vertex has at least `k` neighbours inside the subset (the classical
     "critical graphs have large minimum degree" lemma, proved by a greedy
     re-colouring of the deleted vertex);
  4. `hadwigerProperty_of_minDegree_forces` — hence the minimum-degree statement
     implies `HadwigerProperty k`, using `isMinor_of_isMinor_induce` from
     `HadwigerCore.lean` to lift the minor from the induced subgraph.

  As applications we obtain

  * `completeMinor_three_of_two_le_degree` — the case `k = 2` of the minimum-degree
    statement (minimum degree `2` forces a `K₃` minor), proved from the sharp
    extremal bound of `HadwigerDensity.lean` together with the handshake lemma;
  * `hadwiger_two_via_min_degree` — an independent, degeneracy-flavoured proof of
    `HadwigerProperty 2`;
  * `hadwiger_three_of_dirac` — the `k = 3` instance of the reduction: Dirac's
    theorem "minimum degree `3` forces a `K₄` minor" implies `HadwigerProperty 3`.

  Note that the minimum-degree statement is *strictly stronger* than Hadwiger's
  conjecture for large `k` (it fails for `k` large, by Kostochka's bound), so the
  reduction is genuinely one-directional; for `k ≤ 3` the stronger statement is
  the classical route.

  -- !-- Lab Notes -- !--
  * The greedy re-colouring in step 3 needs `k ≥ 1`; the degenerate case `k = 0`
    is handled separately (`S = univ` works, the degree condition being vacuous).
  * Passing from the `Finset`-level degree `(S.filter (G.Adj v)).card` to
    `Nat.card ((G.induce ↑S).neighborSet ⟨v, hv⟩)` is done through the injective
    image under `Subtype.val`; this is `card_neighborSet_induce`.
-/

open Hadwiger

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-! ## 1.  Colourability of a vertex subset -/




/-! ## 2.  A vertex-minimal non-colourable subset -/


/-! ## 3.  Critical subsets have large minimum degree -/


/-! ## 4.  From `Finset` degrees to degrees of the induced subgraph -/


/-! ## 5.  The reduction -/

theorem Hadwiger.hadwigerProperty_of_minDegree_forces    (H : ∀ (W : Type) [Finite W] [Nonempty W] (K : SimpleGraph W),
        (∀ w : W, k ≤ Nat.card (K.neighborSet w)) → CompleteMinor (k + 1) K) :
    HadwigerProperty k := by sorry
