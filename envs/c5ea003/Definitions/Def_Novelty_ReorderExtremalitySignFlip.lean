-- Prove2me | Definitions.Def_Novelty_ReorderExtremalitySignFlip
-- name    : Novelty_ReorderExtremalitySignFlip
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:36.687049+00:00
-- url     : https://prove2.me/theorems/e71cdbe2-ef6b-4ce4-9f55-9425a371f5ce
-- title:
--   Aether Catalog definitions — Novelty_ReorderExtremalitySignFlip
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ReorderExtremalitySignFlip`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ReorderExtremalitySignFlip.lean by skeleton subtraction
import Mathlib
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

namespace ReorderL7

open Finset

noncomputable section

/-! ## 1.  The REORDER action space and the exchange theorem -/

/-- Expected probe cost of the enumeration `a` against the slot-mass `w`:
the slot visited `k`-th is charged `k+1` probes. -/
def probeCost {n : ℕ} (w : Fin n → ℝ) (a : Equiv.Perm (Fin n)) : ℝ :=
  ∑ k : Fin n, ((k : ℝ) + 1) * w (a k)




/-! ## 2.  The window model for hard-balanced semiprime generators

Write `N = p·q` with `p ≤ q` and balance ratio `r = q/p ∈ [1, 1+δ]`, so that
`p/√N = 1/√r`.  A generator that advertises `q < 2p` licenses the *balance
window* `[√N/√2, √N]`, which the policy commits to ex ante.  Measured in units
of `√N`, a window scan started at the bottom pays `1/√r - 1/√2` and a scan
started at the top pays `1 - 1/√r`. -/

/-- Cost (in units of `√N`) of the window-**ascending** policy on a draw of
balance ratio `r`. -/
def ascCost (r : ℝ) : ℝ := 1 / Real.sqrt r - 1 / Real.sqrt 2

/-- Cost (in units of `√N`) of the window-**descending** policy on a draw of
balance ratio `r`. -/
def descCost (r : ℝ) : ℝ := 1 - 1 / Real.sqrt r

/-- The crossover mean: the value of `E[1/√r]` at which the two window policies
are exactly tied. -/
def crossoverMean : ℝ := (2 + Real.sqrt 2) / 4

/-- The crossover constant in the reciprocal (`E[√r]`) convention of the ledger. -/
def crossoverRecip : ℝ := 4 - 2 * Real.sqrt 2






/-! ### The population law: which order wins is a property of the population -/


/-! ## 3.  The uniform band `r ~ U[1, 1+δ]` : exact mean and closed-form crossover -/

/-- Population mean of `1/√r` for `r` uniform on `[1, 1+δ]`. -/
def meanInvSqrt (delta : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 + delta))



/-- The **population tilt** `z ∈ [0,1]`: the normalised position of the mean hit
inside the balance window.  `z < 1/2` is bottom-heavy (ascending extremal),
`z > 1/2` is top-heavy (descending extremal). -/
def tilt (delta : ℝ) : ℝ := (meanInvSqrt delta - 1 / Real.sqrt 2) / (1 - 1 / Real.sqrt 2)




/-- **The closed-form crossover band width** `δ* = 80 - 56√2`. -/
def crossoverWidth : ℝ := 80 - 56 * Real.sqrt 2





/-! ## 4.  The falsification -/



end

end ReorderL7


