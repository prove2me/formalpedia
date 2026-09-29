-- Prove2me | Definitions.Def_MachineLearning_TotalVariation_Coupling
-- name    : MachineLearning_TotalVariation_Coupling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:13:06.347278+00:00
-- url     : https://prove2.me/theorems/f3fa8aa0-3164-4e68-84d6-40ac4e4500a5
-- title:
--   Aether Catalog definitions — MachineLearning_TotalVariation_Coupling
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TotalVariation.Coupling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TotalVariation/Coupling.lean by skeleton subtraction
import Mathlib
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

namespace UniversalRedundancy

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Couplings -/

/-- `c` is a coupling of the laws `p` and `q`: a joint law on `X × X` with the
prescribed marginals. -/
structure IsCoupling (p q : X → ℝ) (c : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ c x y
  left : ∀ x, ∑ y, c x y = p x
  right : ∀ y, ∑ x, c x y = q y

/-- Probability that the two coordinates of the joint law `c` disagree. -/
def disagreeProb (c : X → X → ℝ) : ℝ := ∑ x, ∑ y, if x = y then 0 else c x y


/-! ## Every coupling dominates the total variation distance -/



/-! ## The maximal coupling -/

open Classical in
/-- The **maximal coupling** of `p` and `q`: keep the shared mass
`min(p, q)` on the diagonal and match the two leftovers independently, rescaled
by `d_TV`. -/
noncomputable def maxCoupling (p q : X → ℝ) : X → X → ℝ := fun x y =>
  (if x = y then min (p x) (q x) else 0)
    + (if tvDist p q = 0 then 0
        else (p x - min (p x) (q x)) * (q y - min (p y) (q y)) / tvDist p q)











end UniversalRedundancy


