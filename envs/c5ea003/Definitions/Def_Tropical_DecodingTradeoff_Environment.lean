-- Prove2me | Definitions.Def_Tropical_DecodingTradeoff_Environment
-- name    : Tropical_DecodingTradeoff_Environment
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:02.384187+00:00
-- url     : https://prove2.me/theorems/96f3dc27-1e1f-4dfb-a06b-a2fbbcd2a564
-- title:
--   Aether Catalog definitions — Tropical_DecodingTradeoff_Environment
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.DecodingTradeoff.Environment`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/DecodingTradeoff/Environment.lean by skeleton subtraction
import Mathlib
/-
# The Bernoulli environment: the probabilistic endpoint of the decoding trade-off

This file builds, from scratch and with no measure theory, the finite Bernoulli product
measure on environments `ω : Fin n → Bool`.  Here `ω i = true` means "step `i` of the
tropical chain is *informative*" (its transfer matrix has small diameter), and
`ω i = false` means the step is *uninformative*.

The decoder of `Tropical.DecodingTradeoff.Tradeoff` with window length `b` fails at a
position only if an entire window of `b` consecutive steps is uninformative.  This file
computes the probability of that event exactly and bounds it from both sides.

## Main results

* `Prob_univ` — the weights `wt p` form a probability distribution (total mass `1`).
* `Prob_badWindow` — the probability that a whole window of length `b` is uninformative
  is **exactly** `(1 - p) ^ b`.
* `prob_failSet_le` — union bound: `Prob p (failSet b) ≤ (n + 1 - b) * (1 - p) ^ b`.
* `prob_failSet_ge` — matching lower bound: `(1 - p) ^ b ≤ Prob p (failSet b)`.

The upper and lower bounds differ only by the polynomial factor `n + 1 - b`; this is
what makes the converse (cost lower bound) of the trade-off possible.
-/


open Finset

namespace Tropical.DecodingTradeoff

/-! ## §0. Two elementary facts about sums of nonnegative terms -/



/-! ## §1. Environments and the Bernoulli product weight -/

variable {n : ℕ}

/-- The Bernoulli weight of an environment: each step is informative with probability `p`. -/
def wt (p : ℝ) (ω : Fin n → Bool) : ℝ := ∏ i, (if ω i then p else 1 - p)

/-- The probability of a finite set of environments. -/
def Prob (p : ℝ) (E : Finset (Fin n → Bool)) : ℝ := ∑ ω ∈ E, wt p ω






/-! ## §2. Uninformative windows -/

/-- The set of positions covered by the window of length `b` starting at `i`. -/
def winSet (n i b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => i ≤ (x : ℕ) ∧ (x : ℕ) < i + b)



/-- The cylinder event "every position in `W` is uninformative". -/
def badSet (n : ℕ) (W : Finset (Fin n)) : Finset (Fin n → Bool) :=
  Fintype.piFinset (fun x : Fin n => if x ∈ W then {false} else Finset.univ)




/-- The event "every step in the window of length `b` starting at `i` is uninformative". -/
def badWindow (n i b : ℕ) : Finset (Fin n → Bool) := badSet n (winSet n i b)





/-- The window-`b` failure event: some window of `b` consecutive steps is uninformative. -/
def failSet (n b : ℕ) : Finset (Fin n → Bool) :=
  (Finset.range (n + 1 - b)).biUnion (fun i => badWindow n i b)



end Tropical.DecodingTradeoff


