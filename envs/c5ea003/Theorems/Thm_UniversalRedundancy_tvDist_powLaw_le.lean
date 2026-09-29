-- Prove2me | Theorems.Thm_UniversalRedundancy_tvDist_powLaw_le
-- name    : UniversalRedundancy.tvDist_powLaw_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:01:28.490807+00:00
-- url     : https://prove2.me/theorems/2049fd12-56c6-44b2-943d-d4de5b58d4ef
-- title:
--   `n`-sample bound.
-- statement:
--   **`n`-sample bound.**  Repeated independent sampling amplifies the
--   distinguishing advantage at most linearly: `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`.
--   This is the total-variation form of the hybrid argument.
--
--   ```lean
--   theorem UniversalRedundancy.tvDist_powLaw_le{p q : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x = 1)
--       (hq0 : ∀ x, 0 ≤ q x) (hq : ∑ x, q x = 1) :
--       ∀ n : ℕ, tvDist (powLaw p n) (powLaw q n) ≤ n * tvDist p q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TotalVariation/Testing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TotalVariation/Testing.lean#L237

-- Thm stub generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Operational consequences of the sharp total-variation normalization

`MachineLearning.TotalVariation.EventSup` proved the factor-`1/2` characterization

`d_TV(p, q) = max_{A} (p(A) − q(A))`.

Here we cash it in.  Three classical pillars of statistical learning theory are
derived, each of them *tight* precisely because the normalization is the sharp
one:

1. **Le Cam's two-point bound.**  For the uniform-prior binary testing problem
   `p` vs `q`, the Bayes error of the best test is exactly `(1 − d_TV)/2`
   (`isLeast_bayesError`).  With the crude `ℓ¹` normalization one would only get
   the vacuous `(1 − ‖p − q‖₁)/2`, which is negative as soon as `‖p − q‖₁ > 1`.
2. **Data processing.**  Post-processing by an arbitrary stochastic channel — in
   particular by any deterministic feature map / statistic — cannot increase
   total variation (`tvDist_channel_le`, `tvDist_map_le`).
3. **Tensorization and sample complexity.**  `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`
   (`tvDist_powLaw_le`), so a learner needs `n ≳ 1/d_TV` i.i.d. samples before it
   can tell the two sources apart at all (`bayesError_powLaw_ge`).

## Main results

* `bayesError_eq_half_one_add_eventGap`, `isLeast_bayesError`,
  `bayesError_ge_half_one_sub_tvDist` — Le Cam;
* `tvDist_channel_le`, `tvDist_map_le` — the data-processing inequality;
* `tvDist_prodLaw_le` — two-factor tensorization (hybrid argument);
* `tvDist_powLaw_le` — the `n`-sample bound by induction;
* `bayesError_powLaw_ge` — the resulting sample-complexity lower bound.

## Application keywords

Le Cam method, hypothesis testing, data processing inequality, tensorization,
sample complexity, indistinguishability, hybrid argument
-/


open Finset

open UniversalRedundancy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ## Le Cam's two-point bound -/





/-! ## The data-processing inequality -/





/-! ## Tensorization -/




/-! ## `n` i.i.d. samples -/

theorem UniversalRedundancy.tvDist_powLaw_le{p q : X → ℝ} (hp0 : ∀ x, 0 ≤ p x) (hp : ∑ x, p x = 1)
    (hq0 : ∀ x, 0 ≤ q x) (hq : ∑ x, q x = 1) :
    ∀ n : ℕ, tvDist (powLaw p n) (powLaw q n) ≤ n * tvDist p q := by sorry
