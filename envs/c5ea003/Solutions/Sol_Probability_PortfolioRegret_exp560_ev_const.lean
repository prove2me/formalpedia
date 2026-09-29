-- Prove2me | solution 1 for Probability.PortfolioRegret.exp560_ev_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:48.245811+00:00
-- url     : https://prove2.me/submissions/3b6b8de6-7b8e-44d3-9257-66eb62323368

-- Sol generated from Probability/PortfolioExp560.lean
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
import Theorems.Thm_Probability_PortfolioRegret_ev_const_eq
import Theorems.Thm_Probability_PortfolioRegret_exp560W_sum
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








theorem classW_sum : ∑ c, classW c = 1 := by
  norm_num [classW, Fin.sum_univ_five]



/-! ## The oracle and the winner shares -/





/-! ## Invisibility of the observable bit -/

theorem obsW_eq (o : Fin 2) : obsW o = 1/2 := by fin_cases o <;> rfl

/-- The fiber of the observation map over `o` is the whole class axis. -/
theorem exp560_fiber (o : Fin 2) :
    (univ.filter (fun x : Fin 5 × Fin 2 => exp560Obs x = o))
      = univ.image (fun c : Fin 5 => (c, o)) := by
  ext x
  obtain ⟨c, b⟩ := x
  simp [exp560Obs, Prod.ext_iff, eq_comm]

theorem exp560_sum_fiber (o : Fin 2) (f : Fin 5 × Fin 2 → ℚ) :
    ∑ x ∈ univ.filter (fun x : Fin 5 × Fin 2 => exp560Obs x = o), f x = ∑ c : Fin 5, f (c, o) := by
  rw [exp560_fiber, Finset.sum_image (fun a _ b _ h => (Prod.ext_iff.mp h).1)]

/-- Averaging the cost of a fixed member over the hidden classes. -/
theorem classW_weighted (s : Fin 5) :
    ∑ c, classW c * (if s = c then (1 : ℚ) else penalty)
      = classW s + (1 - classW s) * penalty := by
  have hpt : ∀ c : Fin 5, classW c * (if s = c then (1 : ℚ) else penalty)
      = classW c * penalty + (if c = s then classW c * (1 - penalty) else 0) := by
    intro c
    by_cases h : c = s
    · subst h; simp; ring
    · simp [h, Ne.symm h]
  rw [Finset.sum_congr rfl (fun c _ => hpt c), Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ s (fun c => classW c * (1 - penalty)), ← Finset.sum_mul, classW_sum]
  simp
  ring

theorem fiberMass_exp560 (o : Fin 2) : fiberMass exp560W exp560Obs o = 1/2 := by
  rw [fiberMass, exp560_sum_fiber o exp560W]
  simp only [exp560W]
  rw [← Finset.sum_mul, classW_sum, one_mul, obsW_eq]

/-- **Invisibility.**  Conditioned on the observable bit, every member of the
portfolio has the *same* mean cost on both fibers: the observation carries no
information about the winner. -/
theorem exp560_invisible : Invisible exp560W exp560Cost exp560Obs exp560Mean := by
  intro o s
  rw [exp560_sum_fiber o (fun x => exp560W x * exp560Cost x s), fiberMass_exp560,
    exp560Mean, ← classW_weighted s]
  have : ∀ c : Fin 5, exp560W (c, o) * exp560Cost (c, o) s
      = (1/2 : ℚ) * (classW c * (if s = c then (1 : ℚ) else penalty)) := by
    intro c
    simp only [exp560W, exp560Cost, obsW_eq]
    ring
  rw [Finset.sum_congr rfl (fun c _ => this c), ← Finset.mul_sum]

/-! ## Static value, regret, and the impotence of every dial -/









open Probability.PortfolioRegret in
theorem solution(s : Fin 5) :
    EV exp560W (fun x => exp560Cost x s) = exp560Mean s :=
  ev_const_eq (obs := exp560Obs) exp560_invisible exp560W_sum s
