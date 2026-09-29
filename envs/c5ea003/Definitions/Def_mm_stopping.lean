-- Prove2me | Definitions.Def_mm_stopping
-- name    : mm_stopping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T20:08:57.977631+00:00
-- url     : https://prove2.me/theorems/269be60d-da93-4833-a5b2-ebd330a7051a
-- title:
--   Stopping rules, strong stationary times, separation distance, and the top-to-random shuffle
-- statement:
--   This file formalizes randomized stopping times and strong stationary times, following Chapter 6 of Levin–Peres–Wilmer, in the trajectory calculus of Mission I: a trajectory of length $t$ is a map $\omega:\{0,\dots,t\}\to V$ with weight $\prod_{i<t}P(\omega_i,\omega_{i+1})$.
--
--   **Stopping rules.** A **stopping rule** assigns to each time $t$ and each trajectory prefix $\omega:\{0,\dots,t\}\to V$ a number $s_t(\omega)\in[0,1]$ — the conditional probability of stopping at time $t$, given the path so far and that no earlier stop occurred. Because $s_t$ sees only the prefix up to time $t$, the rule is automatically adapted; randomized rules (values strictly between $0$ and $1$) are allowed.
--
--   **The law of the stopped chain.** The joint probability of stopping at time $t$ in state $y$, starting from $x$, is the finite sum over trajectories
--   $$\mathbb P_x\{\tau=t,\;X_t=y\}=\sum_{\substack{\omega_0=x,\ \omega_t=y}}\Bigl(\prod_{i<t}P(\omega_i,\omega_{i+1})\Bigr)\Bigl(\prod_{u<t}\bigl(1-s_u(\omega|_{\le u})\bigr)\Bigr)\,s_t(\omega)$$
--   — follow $\omega$, decline to stop at each time $u<t$, then stop at $t$. The tail $\mathbb P_x\{\tau>t\}$ is one minus the mass accumulated up to time $t$.
--
--   **Strong stationary times.** A stopping rule is a **strong stationary time** for the chain started at $x$ when the total stopping mass is $1$ (the stop is almost surely finite; the infinite series is a `tsum`, so this also encodes summability) and for every $t$ and $y$
--   $$\mathbb P_x\{\tau=t,\;X_t=y\}=\mathbb P_x\{\tau=t\}\;\pi(y):$$
--   the stopped position is exactly stationary and independent of the stopping time. The product form avoids any division, so it also covers times of zero stopping mass.
--
--   **Separation distance.** $$s_x(t)=\max_{y\in V}\Bigl(1-\frac{P^t(x,y)}{\pi(y)}\Bigr),$$ the quantity that strong stationary times control from above.
--
--   **The top-to-random shuffle.** A deck of $n$ cards is an arrangement (a permutation listing the deck from top to bottom, position $0$ on top). Removing the top card and reinserting it at position $j$ shifts the intervening cards up by one; the chain performs this with $j$ uniform on $\{0,\dots,n-1\}$, so its transition probability from $x$ to $y$ is $\#\{j:\ y=\text{insert}(x,j)\}/n$. The chapter's stopping rule is also defined: stop one shuffle after the card originally at the bottom first reaches the top — a $\{0,1\}$-valued rule depending on the trajectory only through its initial and second-to-last decks, which the mission proves is a strong stationary time.
--
--   **Conventions.** Division is total ($r/0=0$) and non-summable series sum to $0$; probabilistic content is asserted in the theorems under their hypotheses.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 6, Sections 6.1-6.4, pp. 75-80

import Definitions.Def_mm_path
import Definitions.Def_mm_mixing
import Mathlib.Data.Fintype.Perm

/-!
Randomized stopping times, strong stationary times, and separation distance,
following Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 6.

A randomized stopping time for the chain is presented by its **stopping
rule**: for each time `t` and each length-`t` trajectory `ω`, the number
`s t ω ∈ [0,1]` is the conditional probability of stopping at time `t` given
the trajectory so far and that no stop has occurred earlier (extra
independent randomness is allowed, LPW §6.2.2).  The joint law of
`(τ, X_τ)` is then a finite sum over trajectories, and `τ` may depend on the
starting state through `ω 0`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a length-`t` trajectory to its first `u + 1` states. -/
def pathPrefix {t : ℕ} (ω : Fin (t + 1) → V) (u : Fin t) : Fin (u.val + 1) → V :=
  fun i => ω ⟨i.val, by have h1 := i.isLt; have h2 := u.isLt; omega⟩

/-- A **stopping rule**: `s t ω` is the conditional probability of stopping
at time `t` given the trajectory `ω` up to time `t` and that the stop has not
yet occurred (LPW §6.2.2). -/
def IsStoppingRule (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) : Prop :=
  ∀ (t : ℕ) (ω : Fin (t + 1) → V), 0 ≤ s t ω ∧ s t ω ≤ 1

/-- `P_x{τ = t, X_t = y}` for the randomized stopping time given by the rule
`s`: the trajectory reaches `y` at time `t`, no stop occurred at times
`< t`, and the rule stops at time `t`. -/
def stopAtProb (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (t : ℕ) (y : V) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ω (Fin.last t) = y then
      pathWeight P ω * (∏ u : Fin t, (1 - s u.val (pathPrefix ω u))) * s t ω
    else 0

/-- `P_x{τ > t}` for the randomized stopping time given by the rule `s`. -/
def stopTailProb (P : Matrix V V ℝ) (x : V) (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (t : ℕ) : ℝ :=
  1 - ∑ u ∈ Finset.range (t + 1), ∑ y, stopAtProb P x s u y

/-- A **strong stationary time** for the chain started at `x` (LPW §6.4,
Eq. (6.2)): an almost-surely finite randomized stopping time `τ` such that
`P_x{τ = t, X_τ = y} = P_x{τ = t} π(y)` — i.e. `X_τ` has distribution `π`
and is independent of `τ`. -/
def IsStrongStationaryTime (P : Matrix V V ℝ) (π : V → ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) : Prop :=
  IsStoppingRule s ∧
  (∑' t : ℕ, ∑ y, stopAtProb P x s t y) = 1 ∧
  ∀ (t : ℕ) (y : V), stopAtProb P x s t y = (∑ z, stopAtProb P x s t z) * π y

/-- The **separation distance**
`s_x(t) = max_y [1 − P^t(x,y)/π(y)]` (LPW §6.4, Eq. (6.7)). -/
def sepDist (P : Matrix V V ℝ) (π : V → ℝ) (x : V) (t : ℕ) : ℝ :=
  ⨆ y : V, (1 - (P ^ t) x y / π y)

/-- The deck obtained from `x` by removing the top card (position `0`) and
inserting it at position `j`; cards strictly above the insertion point shift
up by one (LPW §6.1). -/
def topToRandomInsert {n : ℕ} (x : Equiv.Perm (Fin n)) (j : Fin n) : Fin n → Fin n :=
  fun i =>
    if h : i.val < j.val then x ⟨i.val + 1, by have := j.isLt; omega⟩
    else if i = j then x ⟨0, i.pos⟩
    else x i

/-- The **top-to-random shuffle** on decks of `n` cards (states: `x p` is the
card at position `p`, position `0` being the top): remove the top card and
insert it at a uniformly random position (LPW §6.1). -/
def topToRandom (n : ℕ) : Matrix (Equiv.Perm (Fin n)) (Equiv.Perm (Fin n)) ℝ :=
  fun x y =>
    ((Finset.univ.filter fun j : Fin n =>
        ∀ i : Fin n, y i = topToRandomInsert x j i).card : ℝ) / n

/-- The stopping rule for `τ_top`, the time one shuffle after the original
bottom card (the card at position `n-1` of the initial deck `ω 0`) first
reaches the top of the deck (LPW §6.1, §6.5.3). -/
def topToRandomRule (n : ℕ) :
    ∀ t : ℕ, (Fin (t + 1) → Equiv.Perm (Fin n)) → ℝ :=
  fun t ω =>
    if h : 0 < n ∧ 1 ≤ t then
      if (ω ⟨t - 1, by omega⟩) ⟨0, h.1⟩ = (ω 0) ⟨n - 1, by omega⟩ then 1 else 0
    else 0

end

end MarkovMixing


