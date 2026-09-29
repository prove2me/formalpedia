-- Prove2me | solution 1 for Probability.PortfolioRegret.bestConstant_le_of_epsInvisible
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:45:04.632643+00:00
-- url     : https://prove2.me/submissions/4719b949-a71c-4e70-93e2-de7a67060046

-- Sol generated from Probability/PortfolioEpsInvisible.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_ev_const_eq_sum_fiberVal
import Theorems.Thm_Probability_PortfolioRegret_sum_fiberMass
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Quantitative (ε-)invisibility: stability of the no-dial-edge theorem

`Probability.PortfolioRegretCore` proves that an *exactly* invisible observation
is worthless for scheduling: the optimal dial is the do-nothing dial.  Exact
invisibility is a knife-edge hypothesis, and no measurement can ever certify it.
This file replaces it by a measurable one.

An observation is **ε-invisible** for the portfolio when, on every fiber, the
(unnormalised) conditional cost of every member differs from its global
conditional mean `m s` by at most `ε` times the mass of the fiber:

`|fiberVal o s - fiberMass o * m s| ≤ ε * fiberMass o`.

Main results:

* `bestConstant_le_of_epsInvisible` — the best static member costs at most
  `min m + ε`;
* `dialValue_ge_of_epsInvisible` — the *optimal* observation-measurable rule
  costs at least `min m - ε`;
* `eps_invisible_gap_le` — hence `bestConstant - dialValue ≤ 2 * ε`: a small
  measured dial gain is a certificate of near-invisibility, and conversely
  near-invisibility caps the achievable gain.  This is the conjectured
  stability statement of the previous cycle (`FUTURE_DIRECTIONS.md`, direction 1);
* `eps_invisible_policy_ge` — the approximate no-dial-edge inequality for an
  arbitrary rule, degenerating to `no_dial_edge` at `ε = 0`;
* **sharpness**: the explicit "anti-diagonal" portfolios `spreadCost n`
  (`n+1` members, `n+1` fibers, uniform weights, cost `-1` on the diagonal and
  `+1` off it) are `1`-invisible with gap exactly `2 n / (n+1)`
  (`spread_gap`), so the constant `2` cannot be lowered
  (`eps_invisible_two_sharp`), while a *single* fiber pair already forces the gap
  to be at least `ε` (`spread_gap` at `n = 1`).

* **the naive converse fails** (`gap_zero_of_identical_members`,
  `gap_zero_not_epsInvisible`): a portfolio of indistinguishable members has dial
  gain `0` on *every* observation, and an explicit two-instance example with gain
  `0` fails to be `ε`-invisible for any `ε < 1` and any mean profile.  A null dial
  measurement is therefore one-sided evidence only.

Everything is finite and rational; no measure theory is involved.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## ε-invisibility -/



theorem fiberVal_le_of_epsInvisible [Fintype Ω] [DecidableEq O]
    {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ} {eps : ℚ}
    (h : EpsInvisible w cost obs m eps) (o : O) (s : S) :
    fiberVal w cost obs o s ≤ fiberMass w obs o * m s + eps * fiberMass w obs o := by
  have := (abs_le.mp (h o s)).2
  linarith


/-! ## The two ends of the sandwich -/



/-! ## Stability of the no-dial-edge theorem -/




/-! ## Sharpness of the constant `2`

The "anti-diagonal" portfolio on `Fin (n+1)`: instance `o` is its own fiber, the
`o`-th member is the unique winner there (cost `-1`) and every other member pays
`+1`.  All members have the same global mean, so the portfolio is `1`-invisible,
yet an optimal dial saves `2 n / (n + 1)`. -/















/-! ## The naive converse fails

A zero dial gain does **not** certify `eps`-invisibility: if the members of the
portfolio are indistinguishable, no dial can gain anything however unbalanced the
fibers are. -/







open Probability.PortfolioRegret in
theorem solution[Fintype Ω] [Fintype O] [DecidableEq O]
    [Fintype S] [Nonempty S]
    {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ} {eps : ℚ}
    (hw : ∑ ω, w ω = 1) (h : EpsInvisible w cost obs m eps) :
    bestConstant w cost ≤ univ.inf' univ_nonempty m + eps := by
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := S)) m
  have hmass : ∑ o, fiberMass w obs o = 1 := by rw [sum_fiberMass, hw]
  have hb : bestConstant w cost ≤ EV w (fun ω => cost ω s₀) :=
    Finset.inf'_le _ (mem_univ s₀)
  have hEV : EV w (fun ω => cost ω s₀) ≤ ∑ o, fiberMass w obs o * (m s₀ + eps) := by
    rw [ev_const_eq_sum_fiberVal w cost obs s₀]
    refine Finset.sum_le_sum fun o _ => ?_
    have := fiberVal_le_of_epsInvisible h o s₀
    nlinarith [this]
  have hsum : ∑ o, fiberMass w obs o * (m s₀ + eps) = m s₀ + eps := by
    rw [← Finset.sum_mul, hmass, one_mul]
  rw [hs₀]
  linarith [hb, hEV, hsum.le, hsum.ge]
