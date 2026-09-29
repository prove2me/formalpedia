-- Prove2me | Definitions.Def_mm_network
-- name    : mm_network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-21T20:59:26.036633+00:00
-- url     : https://prove2.me/theorems/a162d7c7-0b70-408b-9c9e-9ff7f976e173
-- title:
--   Electrical networks, hitting times, and cover times
-- statement:
--   This file builds the electrical-network dictionary of Chapters 9–11 of Levin–Peres–Wilmer over the trajectory calculus of Mission I (trajectories $\omega:\{0,\dots,t\}\to V$ weighted by $\prod_{i<t}P(\omega_i,\omega_{i+1})$; expectations are tail sums $\sum_{t\ge0}\mathbb P\{\cdot>t\}$).
--
--   **Networks and their walks.** A **network** on a finite vertex set is a conductance function: $c(x,y)\ge0$ and $c(x,y)=c(y,x)$. Writing $c(x)=\sum_yc(x,y)$ for the vertex conductance and $c_G=\sum_xc(x)$ for the total, the **network walk** moves with probabilities
--   $$P(x,y)=\frac{c(x,y)}{c(x)}.$$
--   A function $h$ is **harmonic** on a set of vertices when $h(x)=\sum_yP(x,y)h(y)$ at every $x$ in the set — the mean-value property at those vertices.
--
--   **Voltages and currents, probabilistically.** The file first defines the first-visit law of a set $B$: the probability $\mathbb P_x\{X_{\tau_B}=y\}$ that the walk started at $x$ first meets $B$ at $y$, as a sum of trajectory weights over all lengths. The **voltage** of the network with source $a$ and sink $z$ is the harmonic extension of the boundary values $W(a)=1$, $W(z)=0$, defined probabilistically as
--   $$W(x)=\mathbb P_x\{\tau_a<\tau_z\}.$$
--   The **current strength** flowing out of the source is $\;\|I\|=\sum_y c(a,y)\bigl[W(a)-W(y)\bigr]$, and the **effective resistance** between $a$ and $z$ is $R(a\leftrightarrow z)=\|I\|^{-1}$.
--
--   **Flows.** A **flow** from $a$ to $z$ is an edge function $\theta$ that is antisymmetric ($\theta(x,y)=-\theta(y,x)$), vanishes off the network's edges, and satisfies the node law $\sum_y\theta(x,y)=0$ at every vertex other than $a$ and $z$. Its **strength** is the net flow $\sum_y\theta(a,y)$ out of the source, and its **energy** is
--   $$\mathcal E(\theta)=\tfrac12\sum_{x,y}\frac{\theta(x,y)^2}{c(x,y)}$$
--   (the half counting each undirected edge once). Thomson's principle and the energy characterization of $R(a\leftrightarrow z)$ are theorems of this mission.
--
--   **Green's function, hitting and cover times.** The **Green's function** $G_{\tau_z}(a,x)$ is the expected number of visits to $x$ before hitting $z$, defined as the sum over all $t$ of the probability of being at $x$ at time $t$ without having touched $z$. The extremal hitting time and **cover time** are
--   $$t_{\mathrm{hit}}=\max_{x,y}\ \mathbb E_x(\tau_y),\qquad t_{\mathrm{cov}}=\max_x\ \mathbb E_x(\tau_{\mathrm{cov}}),$$
--   where the expected time to cover — to have visited every vertex — is the tail sum over $t$ of the probability that some vertex remains unvisited at time $t$.
--
--   **Conventions.** Division and inversion are total ($r/0=0$, $0^{-1}=0$) and non-summable series sum to $0$; so all quantities are globally defined, and the finiteness or positivity needed for their probabilistic meaning appears as hypotheses of the accompanying theorems.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 9-11, Sections 9.1-9.4, 10.1-10.3, 11.1, pp. 115-143

import Definitions.Def_mm_path
import Definitions.Def_mm_mixing

/-!
Electrical networks, hitting times, and cover times, following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, Chapters 9–11.

A network is a symmetric nonnegative conductance function `c` on pairs of
vertices; the associated weighted random walk moves with probabilities
`P(x,y) = c(x,y)/c(x)`.  The voltage with unit boundary values at `a` and
`0` at `z` is the harmonic function `W(x) = P_x{τ_a < τ_z}`, and the
effective resistance is `R(a↔z) = [W(a) − W(z)]/‖I‖ = ‖I‖⁻¹`, where `‖I‖`
is the strength of the associated current flow.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **conductance function**: symmetric and nonnegative edge weights
(LPW §9.1). -/
def IsConductance (c : V → V → ℝ) : Prop :=
  (∀ x y : V, 0 ≤ c x y) ∧ ∀ x y : V, c x y = c y x

/-- `c(x) = ∑_y c(x,y)`, the total conductance at a vertex (LPW §9.1). -/
def vertexConductance (c : V → V → ℝ) (x : V) : ℝ :=
  ∑ y, c x y

/-- `c_G = ∑_x c(x)`, twice the total edge conductance (LPW §9.1). -/
def totalConductance (c : V → V → ℝ) : ℝ :=
  ∑ x, vertexConductance c x

/-- The **weighted random walk** on the network:
`P(x,y) = c(x,y)/c(x)` (LPW §9.1, Eq. (9.1)). -/
def networkWalk (c : V → V → ℝ) : Matrix V V ℝ :=
  fun x y => c x y / vertexConductance c x

/-- `h` is harmonic for `P` at every state of `S` (LPW §9.2). -/
def HarmonicOn (P : Matrix V V ℝ) (h : V → ℝ) (S : Set V) : Prop :=
  ∀ x ∈ S, h x = ∑ y, P x y * h y

/-- `P_x{τ_B = t, X_t = y}` (for `y ∈ B`): the chain first meets the set `B`
at time `t`, arriving at `y` (LPW §9.2). -/
def hitSetAtProb (P : Matrix V V ℝ) (x : V) (B : Finset V) (y : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ (∀ i : Fin (t + 1), i ≠ Fin.last t → ω i ∉ B) ∧
        ω (Fin.last t) = y then
      pathWeight P ω
    else 0

/-- `P_x{X_{τ_B} = y}` (for `y ∈ B`): the distribution of the first visit to
the set `B` (LPW §9.2, Proposition 9.1). -/
def firstHitAtProb (P : Matrix V V ℝ) (x : V) (B : Finset V) (y : V) : ℝ :=
  ∑' t : ℕ, hitSetAtProb P x B y t

/-- The **voltage** at `x` when a unit potential is imposed at `a` and zero
potential at `z`: the harmonic function `W(x) = P_x{τ_a < τ_z}`
(LPW §9.3). -/
def voltage (c : V → V → ℝ) (a z x : V) : ℝ :=
  hitBeforeProb (networkWalk c) x a z

/-- The **strength of the unit-voltage current flow** out of `a`:
`‖I‖ = ∑_y c(a,y) [W(a) − W(y)]` for the voltage `W` with `W(a) = 1`,
`W(z) = 0` (LPW §9.3–9.4). -/
def currentStrength (c : V → V → ℝ) (a z : V) : ℝ :=
  ∑ y, c a y * (voltage c a z a - voltage c a z y)

/-- The **effective resistance** `R(a ↔ z) = [W(a) − W(z)]/‖I‖ = ‖I‖⁻¹`
(LPW §9.4, Eq. (9.11)). -/
def effectiveResistance (c : V → V → ℝ) (a z : V) : ℝ :=
  (currentStrength c a z)⁻¹

/-- A **flow from `a` to `z`** on the network: an antisymmetric edge
function, supported on edges of positive conductance, satisfying the node
law at every vertex other than `a` and `z` (LPW §9.3). -/
def IsFlow (c : V → V → ℝ) (θ : V → V → ℝ) (a z : V) : Prop :=
  (∀ x y : V, θ x y = -θ y x) ∧
  (∀ x y : V, c x y = 0 → θ x y = 0) ∧
  ∀ x : V, x ≠ a → x ≠ z → ∑ y, θ x y = 0

/-- The **strength** `‖θ‖ = ∑_y θ(a,y)` of a flow from `a` (LPW §9.3). -/
def flowStrength (θ : V → V → ℝ) (a : V) : ℝ :=
  ∑ y, θ a y

/-- The **energy** `E(θ) = ∑_e θ(e)² r(e)` of a flow (each undirected edge
counted once; LPW §9.4, Thomson's principle). -/
def flowEnergy (c : V → V → ℝ) (θ : V → V → ℝ) : ℝ :=
  2⁻¹ * ∑ x, ∑ y, θ x y ^ 2 / c x y

/-- `P_x{X_t = y, τ_B > t}`: the chain is at `y` at time `t` without having
visited the set `B` at any time `≤ t`. -/
def avoidSetAtProb (P : Matrix V V ℝ) (x : V) (B : Finset V) (y : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ (∀ i : Fin (t + 1), ω i ∉ B) ∧ ω (Fin.last t) = y then
      pathWeight P ω
    else 0

/-- The **Green's function** of the walk stopped at `τ_z`:
`G_{τ_z}(a, x) = E_a(number of visits to x strictly before τ_z)`
(LPW §9.4, Eq. (9.17)). -/
def greenFn (P : Matrix V V ℝ) (a z x : V) : ℝ :=
  ∑' t : ℕ, avoidSetAtProb P a {z} x t

/-- `t_hit = max_{x,y} E_x(τ_y)`, the maximal hitting time (LPW §10.1,
Eq. (10.5)). -/
def hitTimeMax (P : Matrix V V ℝ) : ℝ :=
  ⨆ p : V × V, expSetHitTime P p.1 {p.2}

/-- `P_x{τ_cov > t}`: at time `t`, some state has not yet been visited
(LPW §11.1). -/
def coverTailProb (P : Matrix V V ℝ) (x : V) (t : ℕ) : ℝ :=
  ∑ ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∃ y : V, ∀ i : Fin (t + 1), ω i ≠ y then pathWeight P ω else 0

/-- `E_x(τ_cov)`, the expected time to visit every state, via the tail-sum
formula (LPW §11.1). -/
def expCoverTime (P : Matrix V V ℝ) (x : V) : ℝ :=
  ∑' t : ℕ, coverTailProb P x t

/-- `t_cov = max_x E_x(τ_cov)`, the cover time of the chain (LPW §11.1). -/
def coverTimeMax (P : Matrix V V ℝ) : ℝ :=
  ⨆ x : V, expCoverTime P x

end

end MarkovMixing


