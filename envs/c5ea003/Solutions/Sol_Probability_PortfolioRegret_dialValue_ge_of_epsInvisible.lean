-- Prove2me | solution 1 for Probability.PortfolioRegret.dialValue_ge_of_epsInvisible
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:47:02.542605+00:00
-- url     : https://prove2.me/submissions/e2171fe1-87a8-4b8f-b95c-01b6e1fe8197

-- Sol generated from Probability/PortfolioEpsInvisible.lean
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioEpsInvisible
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_fiberMass_nonneg
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




theorem le_fiberVal_of_epsInvisible [Fintype Ω] [DecidableEq O]
    {w : Ω → ℚ} {cost : Ω → S → ℚ} {obs : Ω → O} {m : S → ℚ} {eps : ℚ}
    (h : EpsInvisible w cost obs m eps) (o : O) (s : S) :
    fiberMass w obs o * m s - eps * fiberMass w obs o ≤ fiberVal w cost obs o s := by
  have := (abs_le.mp (h o s)).1
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
    (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (h : EpsInvisible w cost obs m eps) :
    univ.inf' univ_nonempty m - eps ≤ dialValue w cost obs := by
  have hmass : ∑ o, fiberMass w obs o = 1 := by rw [sum_fiberMass, hw]
  have hlow : ∀ o : O,
      fiberMass w obs o * (univ.inf' univ_nonempty m - eps)
        ≤ univ.inf' univ_nonempty (fiberVal w cost obs o) := by
    intro o
    refine Finset.le_inf' univ_nonempty _ fun s _ => ?_
    have h1 : fiberMass w obs o * m s - eps * fiberMass w obs o ≤ fiberVal w cost obs o s :=
      le_fiberVal_of_epsInvisible h o s
    have h2 : univ.inf' univ_nonempty m ≤ m s := Finset.inf'_le _ (mem_univ s)
    have h3 : (0 : ℚ) ≤ fiberMass w obs o := fiberMass_nonneg hw0 obs o
    nlinarith [h1, h2, h3]
  calc univ.inf' univ_nonempty m - eps
      = ∑ o, fiberMass w obs o * (univ.inf' univ_nonempty m - eps) := by
        rw [← Finset.sum_mul, hmass, one_mul]
    _ ≤ ∑ o, univ.inf' univ_nonempty (fiberVal w cost obs o) :=
        Finset.sum_le_sum fun o _ => hlow o
    _ = dialValue w cost obs := rfl
