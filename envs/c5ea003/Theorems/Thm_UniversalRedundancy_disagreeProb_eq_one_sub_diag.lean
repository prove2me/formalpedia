-- Prove2me | Theorems.Thm_UniversalRedundancy_disagreeProb_eq_one_sub_diag
-- name    : UniversalRedundancy.disagreeProb_eq_one_sub_diag
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:59:13.524887+00:00
-- url     : https://prove2.me/theorems/8abb0a18-a0dc-4390-ad0f-baebcaa5136a
-- title:
--   DisagreeProb eq one sub diag
-- statement:
--   Formal statement of `UniversalRedundancy.disagreeProb_eq_one_sub_diag` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem UniversalRedundancy.disagreeProb_eq_one_sub_diag{p q : X → ℝ} {c : X → X → ℝ}
--       (hc : IsCoupling p q c) (hp : ∑ x, p x = 1) :
--       disagreeProb c = 1 - ∑ x, c x x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Coupling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Coupling.lean#L68

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

theorem UniversalRedundancy.disagreeProb_eq_one_sub_diag{p q : X → ℝ} {c : X → X → ℝ}
    (hc : IsCoupling p q c) (hp : ∑ x, p x = 1) :
    disagreeProb c = 1 - ∑ x, c x x := by sorry
