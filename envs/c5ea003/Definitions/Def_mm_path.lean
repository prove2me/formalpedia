-- Prove2me | Definitions.Def_mm_path
-- name    : mm_path
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T01:41:21.933927+00:00
-- url     : https://prove2.me/theorems/c6b37222-bbab-41e5-b9db-8cf6a9793d66
-- title:
--   Trajectories, return times, and hitting times of a finite chain
-- statement:
--   This file develops the finite-horizon trajectory calculus of a finite chain, following Sections 1.5 and 2.1 of Levin-Peres-Wilmer. A trajectory of length $t$ is a map $\omega:\{0,\dots,t\}\to V$, carrying the weight $\prod_{i<t}P(\omega_i,\omega_{i+1})$; the probability of any event determined by the first $t$ steps of the chain started at $x$ is the finite sum of the weights of the trajectories with $\omega_0=x$ realizing it. In this way the file defines the tail probabilities $\mathbb P_x\{\tau^+_z>t\}$ of the first hitting time $\tau^+_z=\min\{t\ge1:X_t=z\}$ (the starting state is exempt from the avoidance constraint), the refined event $\mathbb P_x\{X_t=y,\ \tau^+_z>t\}$, the tails $\mathbb P_x\{\tau_S>t\}$ of the hitting time $\tau_S=\min\{t\ge0:X_t\in S\}$ of a set of states (here the starting state is **not** exempt), and the first-passage probabilities $\mathbb P_x\{\tau_a=t,\ \tau_b>t\}$. On top of these, expectations of hitting times are defined by the tail-sum formula $$\mathbb E(Y)=\sum_{t\ge0}\mathbb P\{Y>t\},$$ as infinite series in $t$: the expected hitting time $\mathbb E_x(\tau^+_z)$, the expected return time $\mathbb E_x(\tau^+_x)$, and the expected hitting time $\mathbb E_x(\tau_S)$ of a set; and the probability $\mathbb P_x\{\tau_a<\tau_b\}$ of visiting $a$ strictly before $b$ is defined as the series $\sum_{t\ge0}\mathbb P_x\{\tau_a=t,\ \tau_b>t\}$ of first-passage probabilities. All infinite series follow the convention that a non-summable family sums to $0$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Sections 1.5 and 2.1

import Definitions.Def_mm_basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Finite trajectories, return times and hitting times for a finite Markov chain,
following Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, §1.5 and §2.1.

A length-`t` trajectory is a function `ω : Fin (t+1) → V` recording the states
at times `0, 1, …, t`.  Under the chain law started at `x`, the trajectory `ω`
with `ω 0 = x` has probability `∏ i, P (ω i) (ω (i+1))`; every event
depending on the first `t` steps is a finite sum of such products.  Tail
probabilities of hitting times are expressed this way, and expectations are
recovered as `E Y = ∑_{t ≥ 0} P{Y > t}` for a nonnegative integer variable `Y`
(the identity used throughout LPW, e.g. in the proof of Lemma 1.13).
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The probability weight `∏_{i<t} P(ω_i, ω_{i+1})` of the length-`t`
trajectory `ω` (conditional on its starting state `ω 0`). -/
def pathWeight (P : Matrix V V ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ :=
  ∏ i : Fin t, P (ω i.castSucc) (ω i.succ)

/-- `P_x{τ⁺_z > t, X_t = y}`: the chain started at `x` is at `y` at time `t`
without having visited `z` at any of the times `1, …, t` (LPW §1.5.3,
Eq. (1.19), where `τ⁺_z = min {t ≥ 1 : X_t = z}` is the first return time). -/
def avoidHitProb (P : Matrix V V ℝ) (x z y : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z) ∧ ω (Fin.last t) = y then
      pathWeight P ω
    else 0

/-- `P_x{τ⁺_z > t}`: the chain started at `x` does not visit `z` at any of the
times `1, …, t` (LPW §1.5.2). -/
def avoidTailProb (P : Matrix V V ℝ) (x z : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ 0 → ω i ≠ z) then pathWeight P ω else 0

/-- `E_x(τ⁺_z)`, the expected first time `≥ 1` at which the chain started at
`x` visits `z`, via the tail-sum formula `E Y = ∑_{t≥0} P{Y > t}`
(LPW §1.5.2–§1.5.3; junk value `0` when the tails are not summable). -/
def expHitTimePos (P : Matrix V V ℝ) (x z : V) : ℝ :=
  ∑' t : ℕ, avoidTailProb P x z t

/-- `E_x(τ⁺_x)`, the expected first return time to `x` (LPW §1.5.3). -/
def expReturnTime (P : Matrix V V ℝ) (x : V) : ℝ :=
  expHitTimePos P x x

/-- `P_x{τ_a = t, τ_b > t}`: started at `x`, the chain first visits `a` at
time `t` and has not visited `b` at any time `≤ t`.  (Here `τ_a` is the first
time `≥ 0` at which the chain is at `a`.) -/
def firstHitBeforeProb (P : Matrix V V ℝ) (x a b : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = a ∧
        (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ≠ a) ∧ (∀ i : Fin (t + 1), ω i ≠ b) then
      pathWeight P ω
    else 0

/-- `P_x{τ_a < τ_b}`: started at `x`, the chain visits `a` (at some finite
time) strictly before it visits `b` (LPW §2.1). -/
def hitBeforeProb (P : Matrix V V ℝ) (x a b : V) : ℝ :=
  ∑' t : ℕ, firstHitBeforeProb P x a b t

/-- `P_x{τ_S > t}`: the chain started at `x` stays outside the set `S` up to
and including time `t`, where `τ_S = min {t ≥ 0 : X_t ∈ S}`. -/
def setAvoidTailProb (P : Matrix V V ℝ) (x : V) (S : Finset V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ S) then pathWeight P ω else 0

/-- `E_x(τ_S)`, the expected first time `≥ 0` at which the chain started at `x`
is in `S`, via the tail-sum formula (LPW §2.1; junk value `0` when the tails
are not summable). -/
def expSetHitTime (P : Matrix V V ℝ) (x : V) (S : Finset V) : ℝ :=
  ∑' t : ℕ, setAvoidTailProb P x S t

end

end MarkovMixing


