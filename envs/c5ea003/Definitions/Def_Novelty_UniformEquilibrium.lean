-- Prove2me | Definitions.Def_Novelty_UniformEquilibrium
-- name    : Novelty_UniformEquilibrium
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:24.088327+00:00
-- url     : https://prove2.me/theorems/c4612459-546b-4dc9-85c3-96b8cf30a358
-- title:
--   Aether Catalog definitions — Novelty_UniformEquilibrium
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.UniformEquilibrium`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/UniformEquilibrium.lean by skeleton subtraction
import Mathlib

/-!
# Uniform Nash equilibria of finite games with constant strategy sums

This file *deepens* the "Sperner ⇒ Nash" development.  The earlier work established
the algebraic core of finite two–player games (mixed strategies, expected payoffs,
the pure–deviation principle) and verified two concrete games (Matching Pennies and
the Prisoner's Dilemma).  Here we go from *concrete examples* to a *general theorem*:

> **Uniform–equilibrium criterion.**  In a finite two–player game, if each row of
> player 1's payoff matrix has the same total `S1`, and each column of player 2's
> payoff matrix has the same total `S2`, then the *uniform* profile
> `(unif I, unif J)` is a Nash equilibrium, with value `S1 / |J|` to player 1 and
> `S2 / |I|` to player 2.

Against a uniformly randomising opponent, every pure strategy of a "row–constant"
player yields exactly the same payoff, so *every* strategy is a best response — in
particular the uniform one.  This is the finite, combinatorial analogue of the
symmetry argument behind mixed equilibria of symmetric games.

We then instantiate the criterion to obtain, as corollaries in a single stroke:

* Matching Pennies (`matchingPennies_uniform_isNash`),
* Rock–Paper–Scissors (`rps_uniform_isNash`), and
* a whole *parametric family* of cyclic zero–sum games on `ZMod n`
  (`cyclicGame_uniform_isNash`), for **any** payoff generator summing to zero — of
  which Matching Pennies (`n = 2`) and Rock–Paper–Scissors (`n = 3`) are special
  cases, together with the fact that the game value is `0` (`cyclicGame_value`).

## Main results

* `SpernerNashDeep.isNash_of_pure` — pure–deviation principle (chain foundation).
* `SpernerNashDeep.E1_pure_unif` / `E2_pure_unif` — pure payoff vs. a uniform
  opponent is the (normalised) row / column sum.
* `SpernerNashDeep.uniform_isNash_of_row_sum_const` — the general criterion.
* `SpernerNashDeep.E1_value_uniform` / `E2_value_uniform` — the equilibrium value.
* `SpernerNashDeep.cyclicGame_uniform_isNash` / `cyclicGame_value` — the cyclic
  family, its uniform equilibrium and its value.
* `SpernerNashDeep.matchingPennies_uniform_isNash`,
  `SpernerNashDeep.rps_uniform_isNash` — classical special cases.
-/

namespace SpernerNashDeep

open Finset

/-- A finite two–player game: finite strategy sets `I`, `J` and real payoff
matrices `u1`, `u2`. -/
structure FinGame (I J : Type*) [Fintype I] [Fintype J] where
  /-- Payoff to player 1 at the pure profile `(i, j)`. -/
  u1 : I → J → ℝ
  /-- Payoff to player 2 at the pure profile `(i, j)`. -/
  u2 : I → J → ℝ

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A mixed strategy: a probability distribution over a strategy set. -/
def IsDist (p : I → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- The pure strategy `a` viewed as a degenerate mixed strategy. -/
def pureDist [DecidableEq I] (a : I) : I → ℝ := fun i => if i = a then 1 else 0

/-- Expected payoff to player 1 under the mixed profile `(p, q)`. -/
def E1 (G : FinGame I J) (p : I → ℝ) (q : J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * G.u1 i j

/-- Expected payoff to player 2 under the mixed profile `(p, q)`. -/
def E2 (G : FinGame I J) (p : I → ℝ) (q : J → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * G.u2 i j

/-- A profile `(p, q)` is a **Nash equilibrium**. -/
def IsNash (G : FinGame I J) (p : I → ℝ) (q : J → ℝ) : Prop :=
  IsDist p ∧ IsDist q ∧
    (∀ p', IsDist p' → E1 G p' q ≤ E1 G p q) ∧
    (∀ q', IsDist q' → E2 G p q' ≤ E2 G p q)

/-! ### Algebraic core (pure–deviation principle) -/









/-! ### The uniform strategy -/

/-- The uniform mixed strategy on a finite strategy set. -/
noncomputable def unif (I : Type*) [Fintype I] : I → ℝ := fun _ => 1 / (Fintype.card I : ℝ)




/-! ### The uniform–equilibrium criterion -/




/-! ### The cyclic family of zero–sum games -/

/-- The cyclic zero–sum game on `ZMod n` with payoff generator `w`: player 1 gets
`w (i - j)` and player 2 gets `-w (i - j)`.  Matching Pennies (`n = 2`) and
Rock–Paper–Scissors (`n = 3`) are special cases. -/
def cyclicGame (n : ℕ) [NeZero n] (w : ZMod n → ℝ) : FinGame (ZMod n) (ZMod n) where
  u1 i j := w (i - j)
  u2 i j := - w (i - j)





/-! ### Classical special cases -/

/-- Matching Pennies as a cyclic game on `ZMod 2` with generator `w 0 = 1`,
`w 1 = -1`. -/
noncomputable def matchingPennies : FinGame (ZMod 2) (ZMod 2) :=
  cyclicGame 2 (fun k => if k = 0 then 1 else -1)


/-- Rock–Paper–Scissors as a cyclic game on `ZMod 3`: you beat the previous
strategy (`w 1 = 1`), lose to the next (`w 2 = -1`), and tie yourself (`w 0 = 0`). -/
noncomputable def rps : FinGame (ZMod 3) (ZMod 3) :=
  cyclicGame 3 (fun k => if k = 1 then 1 else if k = 2 then -1 else 0)


end SpernerNashDeep


