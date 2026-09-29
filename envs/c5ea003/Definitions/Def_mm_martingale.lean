-- Prove2me | Definitions.Def_mm_martingale
-- name    : mm_martingale
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:00.155341+00:00
-- url     : https://prove2.me/theorems/52402a56-524c-47ea-908e-6d5b966054ba
-- title:
--   Chain martingales and the evolving-set process
-- statement:
--   This file formalizes martingales adapted to a Markov chain and the evolving-set process of Morris and Peres, following Chapter 17 of Levin–Peres–Wilmer, in the trajectory calculus of Missions I and III (trajectories $\omega:\{0,\dots,t\}\to V$ weighted by $\prod_{i<t}P(\omega_i,\omega_{i+1})$).
--
--   **Chain martingales.** A process adapted to the chain is a family $M_t$ of real-valued functions of the trajectory up to time $t$. The family is a **martingale** when its one-step conditional expectation is neutral: for every time $t$ and every trajectory $\omega$ ending at the state $\omega_t$,
--   $$\sum_{y}P(\omega_t,y)\,M_{t+1}(\omega,y)\;=\;M_t(\omega),$$
--   where $(\omega,y)$ is the trajectory extended by one step to $y$. For a finite chain this pointwise finite-sum identity is exactly the measure-theoretic martingale property.
--
--   **Stopped expectations.** For a $\{0,1\}$-valued stopping rule (a non-randomized stopping time in the sense of Mission III) the **expectation of the process at the stopping time**, $\mathbb E_x(M_\tau)$, is the sum over all stopping times $t$ and trajectories from $x$ of (trajectory weight) × (indicator of stopping exactly at $t$) × $M_t(\omega)$ — the quantity governed by the optional stopping theorem.
--
--   **The evolving-set process.** Fix a chain $P$ with stationary distribution $\pi$, and write $Q(S,y)=\sum_{x\in S}\pi(x)P(x,y)$ for the stationary flow from a set $S$ into a state $y$. From the current set $S$, draw $u$ uniform on $(0,1]$ and pass to the superlevel set
--   $$S'=\Bigl\{y:\;\frac{Q(S,y)}{\pi(y)}\ge u\Bigr\}.$$
--   The **evolving-set process** is the Markov chain on subsets of $V$ this rule generates: the transition probability from $S$ to $T$ is the length of the interval of thresholds $u$ whose superlevel set is exactly $T$, encoded by explicit upper and lower endpoints (the smallest clipped ratio over $T$, the largest over $T^c$). States currently receiving much of the flow out of $S$ are likely to join the next set; states receiving little are likely to drop out.
--
--   **Conventions.** Division is total ($r/0=0$) and the stopped expectation is a `tsum` over stopping times (non-summable families sum to $0$; the almost-sure finiteness hypothesis of the theorems is the statement that the stopping mass sums to $1$). The threshold ratios are clipped to $[0,1]$ before the interval lengths are read off, so the evolving-set matrix is defined for arbitrary $P$ and $\pi$; its probabilistic properties are the mission's theorems.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 17, Sections 17.1-17.2 and 17.4, pp. 229-236

import Definitions.Def_mm_stopping
import Definitions.Def_mm_lower

/-!
Martingales with respect to a Markov chain, and the evolving-set process,
following Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapter 17.

A process adapted to the chain is a family `M t : (Fin (t+1) → V) → ℝ` of
functions of the trajectory up to time `t`; the martingale property is the
statement that the conditional expectation of `M (t+1)` given the trajectory
so far equals `M t`, which for a finite chain is a pointwise finite-sum
identity.

The evolving-set process of Morris and Peres is the Markov chain on subsets
of the state space in which, given `S`, the next set is
`{y : Q(S,y)/π(y) ≥ U}` for a uniform `U ∈ (0,1]`, where
`Q(S,y) = ∑_{x ∈ S} π(x)P(x,y)`; its transition probabilities are the
lengths of the corresponding intervals of `U`.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **martingale property** for a process `M` adapted to the chain `P`
(LPW §17.1): for every trajectory prefix, the one-step conditional
expectation of `M (t+1)` equals `M t`. -/
def IsChainMartingale (P : Matrix V V ℝ)
    (M : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) : Prop :=
  ∀ (t : ℕ) (ω : Fin (t + 1) → V),
    ∑ y, P (ω (Fin.last t)) y * M (t + 1) (Fin.snoc ω y) = M t ω

/-- `E_x(M_τ)` for a `{0,1}`-valued stopping rule `s` (a non-randomized
stopping time): the expectation of the process at the stopping time
(LPW §17.2). -/
def stoppedExp (P : Matrix V V ℝ) (x : V)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (M : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ) : ℝ :=
  ∑' t : ℕ, ∑ ω : Fin (t + 1) → V,
    (if ω 0 = x then
      pathWeight P ω * (∏ u : Fin t, (1 - s u.val (pathPrefix ω u))) * s t ω *
        M t ω
    else 0)

/-- `Q(S,y)/π(y)` where `Q(S,y) = ∑_{x∈S} π(x) P(x,y)` — the conditional
probability that `y` belongs to the next evolving set (LPW §17.4,
Eq. (17.13)). -/
def esThresh (P : Matrix V V ℝ) (π : V → ℝ) (S : Finset V) (y : V) : ℝ :=
  (∑ x ∈ S, π x * P x y) / π y

/-- The upper threshold of the interval of `u ∈ (0,1]` for which the
superlevel set of `esThresh P π S` at level `u` equals `T`. -/
def esUpper (P : Matrix V V ℝ) (π : V → ℝ) (S T : Finset V) : ℝ :=
  if h : T.Nonempty then
    T.inf' h fun y => min 1 (max 0 (esThresh P π S y))
  else 1

/-- The lower threshold of the interval of `u ∈ (0,1]` for which the
superlevel set of `esThresh P π S` at level `u` equals `T`. -/
def esLower (P : Matrix V V ℝ) (π : V → ℝ) (S T : Finset V) : ℝ :=
  if h : Tᶜ.Nonempty then
    Tᶜ.sup' h fun y => min 1 (max 0 (esThresh P π S y))
  else 0

/-- The **evolving-set process** (Morris–Peres; LPW §17.4): the Markov chain
on subsets in which, from `S`, the next set is the superlevel set
`{y : Q(S,y)/π(y) ≥ u}` for a uniform `u ∈ (0,1]`. -/
def evolvingSets (P : Matrix V V ℝ) (π : V → ℝ) :
    Matrix (Finset V) (Finset V) ℝ :=
  fun S T => max 0 (esUpper P π S T - esLower P π S T)

end

end MarkovMixing


