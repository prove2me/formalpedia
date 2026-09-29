-- Prove2me | Theorems.Thm_ReorderL7_meanInvSqrt_eq
-- name    : ReorderL7.meanInvSqrt_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:28:15.041918+00:00
-- url     : https://prove2.me/theorems/451ff8a7-517a-406f-9e82-e702167cab18
-- title:
--   The mean is the normalised integral of `r ↦ r^(-1/2)` over the band.
-- statement:
--   The mean is the normalised integral of `r ↦ r^(-1/2)` over the band.
--
--   ```lean
--   theorem ReorderL7.meanInvSqrt_eq{delta : ℝ} (h : 0 < delta) :
--       (1 / delta) * (∫ r in (1:ℝ)..(1 + delta), r ^ (-(1/2) : ℝ)) = meanInvSqrt delta := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ReorderExtremalitySignFlip.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ReorderExtremalitySignFlip.lean#L192

-- Thm stub generated from Novelty/ReorderExtremalitySignFlip.lean
import Mathlib
import Definitions.Def_Novelty_ReorderExtremalitySignFlip
/-
# GAP-L7 falsified and replaced: the extremal enumeration order is a *population*
# property, not a policy-level theorem

This file formalises the first half of the round-76 L7 deliverable: the
**falsification of "√N-descending is the extremal REORDER order"** and its
replacement by the *mass-sorting* theorem plus an exact **sign-flip law** with a
closed-form crossover.

## The action space

A `REORDER`-class policy commits, ex ante, to an enumeration `a₀, a₁, …` of the
candidate index set; test-blindness means the order may not consult the answers
of the probes it schedules.  Formally the object is a permutation of the slots
(`Equiv.Perm (Fin n)`), and the cost charged for a draw whose hit sits at slot
`i` is the number of probes `k+1` with `a k = i`.

## Main results

* `probeCost_masssort_le` (**L7-b, exchange theorem**) — the *mass-sorted*
  enumeration is extremal: if `w ∘ a` is antitone then no re-ordering of `a`
  has smaller expected probe cost.  This is the only order-optimality statement
  the action space supports; it says nothing about `√N`-descending.
* `pop_signflip` — for an arbitrary finite population of balance ratios
  `r = q/p ∈ [1,2)` the window-ascending policy beats the window-descending one
  **iff** `E[1/√r] < (2+√2)/4`; equivalently, in the reciprocal convention of
  the ledger, iff the crossover constant `crossoverRecip = 4 - 2√2 ≈ 1.1716` is
  passed (`crossoverRecip_eq`, `crossoverRecip_bounds`).
* `meanInvSqrt_eq` — for the uniform band `r ~ U[1, 1+δ]` the population mean is
  exactly `E[1/√r] = 2/(1+√(1+δ))` (computed from `∫ r^(-1/2)`).
* `signflip_uniform_band` — the **sign-flip law with closed-form crossover**:
  window-ascending beats window-descending on the band `U[1,1+δ]`
  **iff `δ > 80 - 56√2 ≈ 0.80404`**.
* `hard_balance_tilt`, `hard_balance_ratio` — at hard balance (`q < 2p`, i.e.
  `δ = 1`) the population tilt is exactly `√2 - 1 ≈ 0.4142` (bottom-heavy) and
  descending costs exactly `√2` times ascending.
* `L7_as_drafted_false` — the falsification proper: two admissible balanced
  populations on which the *same* two policies swap winners.  Hence no
  policy-level theorem can name a universal extremal order.

-- !-- Lab Notes -- !--
-- Verifier pools (n = 2400 / 2400 / 1600 / 500): hard-balanced generators come
-- out bottom-heavy with measured tilt z = 0.4095–0.4148 against the analytic
-- value √2 - 1 = 0.41421 proved here (`hard_balance_tilt`); narrow bands come
-- out top-heavy (z ≈ 0.65, matching `meanInvSqrt (1/2)`), descending extremal.
-- The paper-137 pool sits between the two, which is why 137's descending win
-- (asc/desc = 1.078x) is *refined* and not contradicted by this file.
-/

open ReorderL7

open Finset

noncomputable section

/-! ## 1.  The REORDER action space and the exchange theorem -/





/-! ## 2.  The window model for hard-balanced semiprime generators

Write `N = p·q` with `p ≤ q` and balance ratio `r = q/p ∈ [1, 1+δ]`, so that
`p/√N = 1/√r`.  A generator that advertises `q < 2p` licenses the *balance
window* `[√N/√2, √N]`, which the policy commits to ex ante.  Measured in units
of `√N`, a window scan started at the bottom pays `1/√r - 1/√2` and a scan
started at the top pays `1 - 1/√r`. -/










/-! ### The population law: which order wins is a property of the population -/


/-! ## 3.  The uniform band `r ~ U[1, 1+δ]` : exact mean and closed-form crossover -/

theorem ReorderL7.meanInvSqrt_eq{delta : ℝ} (h : 0 < delta) :
    (1 / delta) * (∫ r in (1:ℝ)..(1 + delta), r ^ (-(1/2) : ℝ)) = meanInvSqrt delta := by sorry
