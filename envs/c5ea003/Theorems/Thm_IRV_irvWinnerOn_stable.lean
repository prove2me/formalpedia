-- Prove2me | Theorems.Thm_IRV_irvWinnerOn_stable
-- name    : IRV.irvWinnerOn_stable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:28.429935+00:00
-- url     : https://prove2.me/theorems/71b2ba8e-4cdb-4916-9c7f-43ed17c8f612
-- title:
--   IrvWinnerOn stable
-- statement:
--   Formal statement of `IRV.irvWinnerOn_stable` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem IRV.irvWinnerOn_stable{m : ℕ}
--       {v v' : Fin m → ℝ}
--       (S : Finset (Fin m)) (hS : S.Nonempty)
--       {ε γ : ℝ}
--       (hcert : EliminationGapCertified S hS v γ)
--       (hε : 0 ≤ ε)
--       (hgap : 2 * ε < γ)
--       (hclose : ∀ i, |v' i - v i| ≤ ε) :
--       irvWinnerOn S hS v' = irvWinnerOn S hS v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/IRVStability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/IRVStability.lean#L195

-- Thm stub generated from Bridges/IRVStability.lean
import Mathlib
import Definitions.Def_Bridges_IRVStability
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL3 Tropical Satake Certified Robustness for IRV Classifiers

This file formalizes a robustness theory for deterministic, tie-free
instant-runoff / sequential-elimination classifiers built from multiclass
tropical score maps.

## Main results

* `roundLoser_eq_of_strict_min` — uniqueness of the minimizer on a finite set
* `gap_preserved_under_perturbation` — the one-round perturbation lemma
* `eliminationOrderOn_stable` — elimination-order stability under bounded perturbation
* `irvWinnerOn_stable` — winner stability under bounded perturbation
* `irvWinner_certified_robust` — the full tropical/Lipschitz robustness corollary

## Proof architecture

The core theorem proceeds by induction on the cardinality of the active
candidate set. At each round, the gap certificate ensures the current loser
has score at least γ below every other active candidate. A uniform
perturbation of size ≤ ε shifts each score by at most ε, so the gap shrinks
by at most 2ε. When 2ε < γ, the same candidate remains the unique loser,
and the induction carries through the remaining rounds.
-/


open IRV

open Finset

/-! ## Part 1: Core Definitions -/




/-! ## Part 2: Properties of `roundLoser` -/



/-
If `i ∈ S` is strictly below every other element of `S` under `v`,
    then `roundLoser S hS v = i`.
-/

/-! ## Part 3: Recursive Elimination -/







/-! ## Part 4: One-Round Perturbation Lemma -/

/-
The algebraic heart: if `i` has gap `γ` in `S` under `v`, and `v'` is
    within `ε` of `v` coordinatewise, then `i` still has gap `γ - 2*ε`
    in `S` under `v'`.
-/

/-
From a preserved positive gap, the same candidate is the strict minimizer.
-/

/-! ## Part 5: Main Stability Theorem -/

/-
**Elimination-order stability theorem.** If the elimination of `v` on `S`
    is gap-certified with parameter `γ`, and `v'` is within `ε` of `v`
    coordinatewise with `2ε < γ`, then the elimination order of `v'` on `S`
    equals that of `v`.
-/

/-! ## Part 6: Winner Stability -/

/-
**Winner stability theorem.** Under the same hypotheses as
    `eliminationOrderOn_stable`, the IRV winner is preserved.
-/

theorem IRV.irvWinnerOn_stable{m : ℕ}
    {v v' : Fin m → ℝ}
    (S : Finset (Fin m)) (hS : S.Nonempty)
    {ε γ : ℝ}
    (hcert : EliminationGapCertified S hS v γ)
    (hε : 0 ≤ ε)
    (hgap : 2 * ε < γ)
    (hclose : ∀ i, |v' i - v i| ≤ ε) :
    irvWinnerOn S hS v' = irvWinnerOn S hS v := by sorry
