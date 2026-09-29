-- Prove2me | Theorems.Thm_UniversalRedundancy_isCoupling_maxCoupling
-- name    : UniversalRedundancy.isCoupling_maxCoupling
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:59:20.474837+00:00
-- url     : https://prove2.me/theorems/69f09ab0-a16a-4e30-ac5e-a62e822843b3
-- title:
--   The maximal coupling really is a coupling.
-- statement:
--   The maximal coupling really is a coupling.
--
--   ```lean
--   theorem UniversalRedundancy.isCoupling_maxCoupling{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
--       (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
--       IsCoupling p q (maxCoupling p q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Coupling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Coupling.lean#L169

-- Thm stub generated from MachineLearning/TotalVariation/Coupling.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_EventSup
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coupling (Strassen) characterization of total variation

Third leg of the sharp-normalization thread.  `EventSup` characterized

`d_TV(p, q) = max_A (p(A) − q(A))`

as a supremum over *events*, and `Testing` cashed that in for hypothesis
testing.  This file proves the dual, *infimum*, characterization:

`d_TV(p, q) = min_{couplings c of (p, q)} ℙ_c[X ≠ Y]`.

Both directions are proved:

* every coupling has disagreement probability at least `d_TV`
  (`tvDist_le_disagreeProb`), by pushing the optimal *event* of `EventSup`
  through the coupling — so the two characterizations are genuinely dual;
* the explicit **maximal coupling**

  `c(x, y) = min(p x, q x)·[x = y] + (p x − min)₊ (q y − min)₊ / d_TV`

  attains it (`isCoupling_maxCoupling`, `disagreeProb_maxCoupling`).

The two together give `isLeast_disagreeProb`, and the sandwich
`max_A (p(A) − q(A)) = d_TV = min_c ℙ_c[X ≠ Y]` (`max_eventGap_eq_min_disagree`)
— a minimax identity whose two sides are witnessed by explicit optima.

The factor `1/2` is exactly what makes this work: with the `ℓ¹` normalization the
identity would read `min_c ℙ[X ≠ Y] = ‖p − q‖₁/2`, and the naive `ℓ¹` bound would
be off by two.

## Main results

* `IsCoupling`, `disagreeProb` — the coupling framework;
* `tvDist_le_disagreeProb` — the easy (but event-driven) direction;
* `isCoupling_maxCoupling`, `disagreeProb_maxCoupling` — the maximal coupling;
* `isLeast_disagreeProb`, `max_eventGap_eq_min_disagree` — the minimax identity;
* `eventGap_le_disagreeProb` — the coupling bound on distinguishing advantage.

## Application keywords

maximal coupling, Strassen's theorem, total variation, transport, minimax,
distinguishing advantage
-/


open Finset

open UniversalRedundancy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Couplings -/




/-! ## Every coupling dominates the total variation distance -/



/-! ## The maximal coupling -/

theorem UniversalRedundancy.isCoupling_maxCoupling{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ x, 0 ≤ q x) :
    IsCoupling p q (maxCoupling p q) := by sorry
