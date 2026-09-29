-- Prove2me | Theorems.Thm_SymmetryBreakingCost_exists_prescribed_signature
-- name    : SymmetryBreakingCost.exists_prescribed_signature
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:38:08.854709+00:00
-- url     : https://prove2.me/theorems/162f57b3-b2f4-4b42-afbf-89ab863092f8
-- title:
--   Full independence of Legendre signatures.
-- statement:
--   **Full independence of Legendre signatures.**  For any finite set `S` of distinct odd primes
--   and any prescribed pattern of signs `e`, one single integer realises that pattern:
--   `J(x | p) = 1` if `e p` and `= -1` otherwise, simultaneously for all `p ∈ S`.
--
--   Equivalently: the map `x ↦ (J(x | p))_{p ∈ S}` is onto `{±1}^S`.  This is the exact sense in
--   which the residue battery of the hidden factor is an *unconstrained* fingerprint.
--
--   ```lean
--   theorem SymmetryBreakingCost.exists_prescribed_signature(S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
--       (e : ℕ → Bool) : ∃ x : ℤ, ∀ p ∈ S, J(x | p) = if e p then 1 else -1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/SymmetryBreakingCostFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/SymmetryBreakingCostFactoring.lean#L111

-- Thm stub generated from Novelty/SymmetryBreakingCostFactoring.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring

/-!
# The symmetry-breaking cost of factoring, measured

Let `N` be an odd semiprime and let `S` be the set of candidate prime factors (say, the odd
primes `p` with `p² ≤ N`).  A *battery* is a finite tuple `a : Fin k → ℤ` of test integers.
Two things can be measured with such a battery.

* **Asymmetric (oracle) data.**  An oracle answering with the *Legendre* symbols
  `[(a i | p₀)]` of the hidden factor `p₀`.  The signature `qsig a p = (J(a i | p))ᵢ` is then a
  fingerprint of a candidate, and isolating `p₀` costs exactly as many queries as the
  information-theoretic minimum `⌈log₂ |S|⌉`.
* **Symmetric (public) data.**  The Jacobi symbols `[(a i | N)]` computable from `N` alone.
  These prune *nothing*: every candidate `r` admits a compensating partner making it consistent
  with the whole battery.

The gap between the two is the "symmetry-breaking cost".  This file makes all three sides of
that statement into theorems.

## Main results

* `exists_prescribed_signature` (independence / CRT surjectivity): for any finite set `S` of
  distinct odd primes and any prescribed sign pattern `e : ℕ → Bool` there is a single integer
  `x` with `J(x | p) = ±1` according to `e p`, simultaneously for all `p ∈ S`.  The Legendre
  signatures of distinct primes are completely unconstrained by one another.
* `exists_isolating_battery`: if `|S| ≤ 2 ^ k` there is an admissible battery of size `k` whose
  signature map is injective on `S` — `k` queries isolate every candidate.
* `info_lower_bound`: no `k`-tuple of queries with answers in a finite alphabet `β` can separate
  more than `(card β) ^ k` candidates.
* `isolationCost_isLeast`: **the exact measurement.**  The set of achievable battery sizes has
  least element `Nat.clog 2 |S|`, i.e. the isolation cost is exactly `⌈log₂ |S|⌉`.
* `isolation_cost_le_of_le_four_pow`: for candidates below `√N` this cost is at most `½ log₂ N`.
* `factor_of_isolated`: an isolated candidate that divides `N` yields a nontrivial factorisation.
* `zero_pruning`, `compensating_partner`, `unboundedly_many_survivors`: the symmetric battery
  `[(a i | N)]` eliminates no candidate whatsoever.
* `factor_of_nontrivial_sqrt_one`, `factor_of_even_order`: the *asymmetric* readout of Shor's
  algorithm (an element of even multiplicative order whose half-power is not `±1`) converts into
  a nontrivial factor by a gcd — the quantum payment for the same symmetry breaking.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the quadratic-residue signature of a prime is "generic": knowing the
signatures of all other primes tells you nothing about `p₀`'s.  If true, the signature map is a
perfect binary code on the candidate set and the isolation cost must equal `⌈log₂ |S|⌉` exactly,
with no slack in either direction.

Experiment (Experimenter): computed in `ComputationalEvidence.md`.  For the candidate sets of
`N = 3149 = 47·67`, `N = 10403 = 101·103` and `N = 1000003·1000033` truncated to the primes
below `√N`, greedy batteries of size `⌈log₂ π(√N)⌉` separated all candidates in every trial,
and no battery of size `⌈log₂ π(√N)⌉ - 1` ever did (pigeonhole).  Ratio (queries used) /
`log₂ π(√N)` stayed in `[1, 1.03]`.

Analysis (Analyst): both halves are structural, not statistical.  The upper bound is CRT:
sign patterns of distinct primes are independent, so the signature map can realise *any*
injection `S ↪ {±1}^k`.  The lower bound is pigeonhole on the answer alphabet.  Hence the
measurement `⌈log₂ |S|⌉` is exact, not asymptotic.

Critique (Critic): the lower bound must be stated for the alphabet actually used.  A Jacobi
symbol has three values, and a `0` answer is itself a factor disclosure; we therefore define
`Admissible` batteries (no `0` answers) for the exact `log₂` statement and record the general
ternary bound `info_lower_bound` separately.  No theorem below is vacuous: `isolationCost_mem`
exhibits the battery, and `zero_pruning` is proved for arbitrary candidates.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols

/-! ## 0.  Chinese remainder input -/



/-! ## 1.  Independence of quadratic signatures -/

theorem SymmetryBreakingCost.exists_prescribed_signature(S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (e : ℕ → Bool) : ∃ x : ℤ, ∀ p ∈ S, J(x | p) = if e p then 1 else -1 := by sorry
