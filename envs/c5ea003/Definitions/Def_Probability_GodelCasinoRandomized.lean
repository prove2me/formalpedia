-- Prove2me | Definitions.Def_Probability_GodelCasinoRandomized
-- name    : Probability_GodelCasinoRandomized
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:34.027132+00:00
-- url     : https://prove2.me/theorems/5ddff151-06b4-45e8-bd0f-8e2046f52594
-- title:
--   Aether Catalog definitions — Probability_GodelCasinoRandomized
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GodelCasinoRandomized`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GodelCasinoRandomized.lean by skeleton subtraction
import Mathlib
/-
# Gödel's Casino: randomized strategies and the minimax value

This file continues the "Gödel's Casino" thread. Earlier developments
(`Catalog/NumberTheory/GodelCasino.lean` and
`Catalog/output-final_aristotle/Logic/GodelCasino.lean`) studied *deterministic*
Boolean bets: they proved a deterministic no-free-lunch theorem (complementing a
world negates the payoff) and a sharp *conditional* expected-profit criterion
(positive expectation requires aggregate accuracy `> 1/2`).

Here we take the next step listed under "Further formalization": we formalize
**randomized strategies** on a finite space of possible worlds and prove a
minimax / no-free-lunch theorem against **complement-symmetric priors**, together
with the sharp information-theoretic profitability threshold.

## The model

Fix a finite world space `W`. A statement is `s : W → Bool`. A *randomized
strategy* is a single number `r ∈ [0,1]`: the probability the player bets `true`.
Against the truth value in a world, the expected payoff (over the player's own
coin) is `randPayoff s r ω`, and against a prior `μ : W → ℚ` over worlds it is
`expRand μ s r = ∑ ω, μ ω * randPayoff s r ω`.

## Main results

* `randPayoff_eq` : per-world expected payoff is `2r-1` if true, `1-2r` if false.
* `randPayoff_half` : the **fair coin** `r = 1/2` pays exactly `0` in *every*
  world — a strategy that cannot lose (nor win).
* `expRand_eq` : the exact closed form
  `expRand μ s r = (2r-1) · (trueMass μ s − falseMass μ s)`; the expected profit
  is *bilinear* in the strategy and the prior's truth–falsehood imbalance.
* `expRand_normalized` : for a probability prior, `= (2r-1)·(2·π − 1)` where
  `π = trueMass` is the probability the statement is true.
* `symmetric_prior_zero` : **randomized no-free-lunch.** If the prior admits a
  truth-flipping, mass-preserving involution, then *every* strategy nets exactly
  `0`. Incompleteness modelled as a symmetric prior gives no edge, even with
  randomization.
* `no_benefit_randomization` / `optimal_pure_value` : deterministic (pure) bets
  are optimal, and the optimal value is `|trueMass − falseMass|`. Randomization
  never helps a player who knows the prior.
* `edge_iff_asymmetric` : **edge iff information.** A positive-expectation
  strategy exists *iff* the prior is asymmetric between truth and falsehood. The
  entire edge is the prior's imbalance — decidability/independence per se
  supplies none.
* `deckValue_nonneg`, `deckValue_card_le` : over a deck, the optimal total value
  is the sum of per-card imbalances; it is nonnegative and dominated card by
  card.

The development is elementary and fully self-contained (finite sums over `ℚ`).
-/

namespace GodelCasinoRandomized

open Finset

variable {W : Type*} [Fintype W]

/-- Per-world payoff of the pure bet `b` on statement `s`: `+1` if it matches the
truth value in world `ω`, `-1` otherwise. -/
def payoff (s : W → Bool) (b : Bool) (ω : W) : ℚ := if b = s ω then 1 else -1

/-- Expected payoff (over the player's own randomization) of the strategy that
bets `true` with probability `r` on statement `s`, in world `ω`. -/
def randPayoff (s : W → Bool) (r : ℚ) (ω : W) : ℚ :=
  r * payoff s true ω + (1 - r) * payoff s false ω



/-- Expected profit of strategy `r` on statement `s` under prior `μ` over worlds. -/
def expRand (μ : W → ℚ) (s : W → Bool) (r : ℚ) : ℚ := ∑ ω, μ ω * randPayoff s r ω

/-- Prior mass on the worlds where `s` is true. -/
def trueMass (μ : W → ℚ) (s : W → Bool) : ℚ := ∑ ω, if s ω then μ ω else 0

/-- Prior mass on the worlds where `s` is false. -/
def falseMass (μ : W → ℚ) (s : W → Bool) : ℚ := ∑ ω, if s ω then 0 else μ ω













/-! ## Aggregate over a deck of statements

Playing one optimally-chosen pure bet per card of a deck (over a shared world
prior), the guaranteed total value is the sum of the per-card imbalances. -/

/-- Optimal total value of a deck: the sum of per-card absolute imbalances. -/
def deckValue (μ : W → ℚ) (deck : List (W → Bool)) : ℚ :=
  (deck.map (fun s => |trueMass μ s - falseMass μ s|)).sum



/-! ## Worked example: the two-world casino

On `W = Bool` with the uniform prior and the statement `s = id`, the world-flip
involution `not` is truth-flipping and mass-preserving, so *every* strategy nets
`0` — recovering, for randomized play, the contrarian verdict of the earlier
possible-world file. -/


end GodelCasinoRandomized


