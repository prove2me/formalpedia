-- Prove2me | Theorems.Thm_UniversalRedundancy_tvDist_le_disagreeProb
-- name    : UniversalRedundancy.tvDist_le_disagreeProb
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:01:23.544531+00:00
-- url     : https://prove2.me/theorems/953dfb65-e74f-4f3b-b9a1-0749a33ae24d
-- title:
--   Coupling lower bound.
-- statement:
--   **Coupling lower bound.**  Every coupling of `p` and `q` disagrees with
--   probability at least `d_TV(p, q)`.  The proof runs the optimal *event* of the
--   supremum characterization through the coupling, so the sharp constant here is
--   inherited from the sharp normalization.
--
--   ```lean
--   theorem UniversalRedundancy.tvDist_le_disagreeProb{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
--       {c : X → X → ℝ} (hc : IsCoupling p q c) : tvDist p q ≤ disagreeProb c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Coupling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Coupling.lean#L115

-- Thm stub generated from MachineLearning/TotalVariation/Coupling.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_Coupling
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
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

theorem UniversalRedundancy.tvDist_le_disagreeProb{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1)
    {c : X → X → ℝ} (hc : IsCoupling p q c) : tvDist p q ≤ disagreeProb c := by sorry
