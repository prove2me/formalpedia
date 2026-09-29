-- Prove2me | solution 1 for Probability.PortfolioRegret.exp560_no_universal_winner
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:48.906991+00:00
-- url     : https://prove2.me/submissions/8bff84ee-e5f8-426f-b727-c1623437de14

-- Sol generated from Probability/PortfolioExp560.lean
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The exp-560 portfolio: an exact rational model of the measured winner shares

A concrete instance of the theory of `Probability.PortfolioRegretCore`, built so
that its numbers coincide *exactly* with the measured ones of experiment 560:

| member (index)        | oracle winner share |
| --------------------- | ------------------- |
| `ρ` (Pollard rho, 0)  | `0.580`             |
| `p-1 @ 256` (1)       | `0.345`             |
| `PM1 @ 1024` (2)      | `0.045`             |
| Fermat (3)            | `0.028`             |
| trial division (4)    | `0.002`             |

The instance space is `Fin 5 × Fin 2`: the first coordinate is the *hidden*
`p-1` powersmoothness class (which member of the portfolio will win), the second
is an *observable* bit (a bit-length / balance quintile marker), drawn
independently of the class.  Every member costs `1` on the class it wins and the
common penalty `1179/140` elsewhere.

The verified consequences are:

* `exp560_winner_shares` — the oracle winner shares are exactly the table above;
* `exp560_no_universal_winner` — every member loses on a set of positive mass,
  so no member dominates the portfolio;
* `exp560_staticRegret` — the static regret against the oracle is exactly
  `3.117`, matching the measured value;
* `exp560_no_dial_edge` — *no* rule reading the observable bit beats the best
  static member: a tuned dial provably tunes itself to do-nothing;
* `exp560_ml_rule_strictly_worse` — the two-armed "learned" rule is strictly
  worse, with expected cost exactly `279385/56000 ≈ 4.989`;
* `exp560_probe_threshold` — a probe that reveals the hidden smoothness class is
  worth its price exactly when the price is below `3.117`.
-/

open Probability.PortfolioRegret

open Finset

/-! ## The model -/











/-! ## The oracle and the winner shares -/

/-- The oracle always finishes at cost `1`: some member of the portfolio wins on
every hidden class. -/
theorem exp560_oracle (x : Fin 5 × Fin 2) : oracleCost exp560Cost x = 1 := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ ?_)
  · have : exp560Cost x x.1 = 1 := by simp [exp560Cost]
    exact this ▸ Finset.inf'_le _ (mem_univ x.1)
  · intro s _
    by_cases h : s = x.1
    · simp [exp560Cost, h]
    · simp only [exp560Cost, if_neg h, penalty]
      norm_num




/-! ## Invisibility of the observable bit -/







/-! ## Static value, regret, and the impotence of every dial -/









open Probability.PortfolioRegret in
theorem solution(s : Fin 5) :
    (∃ x : Fin 5 × Fin 2, oracleCost exp560Cost x < exp560Cost x s) ∧
    0 < ∑ x ∈ univ.filter (fun x : Fin 5 × Fin 2 => x.1 = s), exp560W x := by
  constructor
  · refine ⟨(s + 1, 0), ?_⟩
    have hne : s ≠ s + 1 := by
      fin_cases s <;> decide
    rw [exp560_oracle, exp560Cost, if_neg hne, penalty]
    norm_num
  · have : (univ.filter (fun x : Fin 5 × Fin 2 => x.1 = s)) = {(s, 0), (s, 1)} := by
      ext x
      obtain ⟨c, b⟩ := x
      fin_cases b <;> simp [Prod.ext_iff]
    rw [this]
    fin_cases s <;> norm_num [exp560W, classW, obsW]
