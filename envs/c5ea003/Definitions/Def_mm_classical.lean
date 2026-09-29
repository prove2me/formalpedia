-- Prove2me | Definitions.Def_mm_classical
-- name    : mm_classical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T01:41:34.181436+00:00
-- url     : https://prove2.me/theorems/1d013452-762b-4d31-9e6e-5bd5723ee86a
-- title:
--   The gambler's ruin chain, the coupon collector, and simple random walk on $\mathbb{Z}$
-- statement:
--   This file presents the classical chains of Chapter 2 of Levin-Peres-Wilmer directly through their driving randomness, so that all probabilities are elementary counting.
--
--   The **gambler's ruin** chain on $\{0,1,\dots,n\}$ moves from each interior state to its two neighbours with probability $\tfrac12$ each and is absorbed at $0$ and at $n$.
--
--   For the **coupon collector** with $n$ types, the probability $\mathbb P\{\tau>t\}$ that $t$ independent uniform draws fail to collect every type is the fraction of the $n^t$ draw sequences $d:\{1,\dots,t\}\to\{1,\dots,n\}$ that are not surjective, and the expected collection time $\mathbb E(\tau)$ is the tail sum $\sum_{t\ge0}\mathbb P\{\tau>t\}$, an infinite series with the convention that a non-summable family sums to $0$.
--
--   **Simple random walk on $\mathbb Z$** started at $k$ is presented by sign strings: to a string $\omega\in\{\pm1\}^r$ of steps is associated the deterministic position $k+\sum_{i<\min(t,r)}\omega_i$ after $t$ steps, and probabilities of walk events are counts of the $2^r$ equally likely sign strings, taken in the theorems that use these definitions.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Sections 2.1, 2.2 and 2.7

import Definitions.Def_mm_path
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
The classical chains of Levin–Peres–Wilmer, *Markov Chains and Mixing Times*,
Chapter 2: the gambler's ruin chain (§2.1), the coupon-collector process
(§2.2), and simple random walk on `ℤ` (§2.7).

The coupon collector and the walk on `ℤ` are presented directly by their
driving randomness — uniform draws `Fin t → Fin n`, respectively uniform sign
sequences `Fin r → Bool` — so that all probabilities are elementary counting.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

/-- The **gambler's ruin** chain on `{0, 1, …, n}`: fair ±1 steps at the
interior states, absorption at `0` and at `n` (LPW §2.1). -/
def gamblersChain (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k l =>
    if k = 0 ∨ k = Fin.last n then (if l = k then 1 else 0)
    else if l.val = k.val + 1 ∨ l.val + 1 = k.val then 1 / 2 else 0

/-- `P{τ > t}` for the **coupon collector** with `n` coupon types: the
probability that `t` independent uniform draws miss at least one type, i.e.
the fraction of functions `Fin t → Fin n` that are not surjective (LPW §2.2). -/
def couponMissProb (n t : ℕ) : ℝ :=
  ((Finset.univ.filter fun d : Fin t → Fin n => ¬Function.Surjective d).card : ℝ) / n ^ t

/-- `E(τ)` for the coupon collector with `n` types, via the tail-sum formula
`E τ = ∑_{t ≥ 0} P{τ > t}` (LPW §2.2). -/
def couponExpTime (n : ℕ) : ℝ :=
  ∑' t : ℕ, couponMissProb n t

/-- The position at time `t` of the **simple random walk on `ℤ`** started at
`k`, driven by the sign sequence `ω` (`true` = step `+1`, `false` = step `-1`);
each `ω : Fin r → Bool` is equally likely (LPW §2.7). -/
def srwPos {r : ℕ} (k : ℤ) (ω : Fin r → Bool) (t : ℕ) : ℤ :=
  k + ∑ i : Fin r, if (i : ℕ) < t then (if ω i then 1 else -1) else 0

end

end MarkovMixing


