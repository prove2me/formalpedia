-- Prove2me | Definitions.Def_mm_cutoff
-- name    : mm_cutoff
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-22T17:26:53.323737+00:00
-- url     : https://prove2.me/theorems/a6045edc-9167-4a1a-823e-4d5f1c76c0d1
-- title:
--   Cutoff, cutoff windows, and lamplighter chains
-- statement:
--   This file defines the cutoff phenomenon for families of chains (Chapter 18 of Levin–Peres–Wilmer) and the lamplighter chains (Chapter 19), on top of the yardsticks of Missions II–III ($d(t)$, $t_{\mathrm{mix}}(\varepsilon)$, separation distance) and the walk quantities of Mission VI.
--
--   **Cutoff.** A **family of chains** is a sequence $P^{(n)}$ on state spaces $V_n$ with distinguished distributions $\pi_n$. The family has a **cutoff** when, for every $0<\varepsilon<1$,
--   $$\frac{t^{(n)}_{\mathrm{mix}}(\varepsilon)}{t^{(n)}_{\mathrm{mix}}(1-\varepsilon)}\;\longrightarrow\;1\qquad(n\to\infty):$$
--   the time to get quite well mixed and the time to get barely mixed agree to leading order — convergence is abrupt rather than gradual.
--
--   **Cutoff windows.** The family has a **cutoff at $t_n$ with window $w_n$** when $w_n/t_n\to0$ and, evaluating the worst-case distance $d_n$ at the times $\lfloor t_n+\alpha w_n\rfloor$,
--   $$\lim_{\alpha\to-\infty}\ \liminf_{n\to\infty}\ d_n(\lfloor t_n+\alpha w_n\rfloor)=1,\qquad \lim_{\alpha\to+\infty}\ \limsup_{n\to\infty}\ d_n(\lfloor t_n+\alpha w_n\rfloor)=0:$$
--   sufficiently far before $t_n$ (in units of $w_n$) the family is asymptotically unmixed, sufficiently far after it is asymptotically mixed. The **maximal separation distance** $s(t)=\max_xs_x(t)$ (with $s_x$ the separation distance of Mission III) and the corresponding **separation cutoff** are defined by the same window template with $s$ in place of $d$.
--
--   **The biased segment walk.** The lazy walk on $\{0,\dots,n\}$ with up-probability $p$: from an interior state, hold with probability $\tfrac12$, step up with probability $p/2$, down with probability $(1-p)/2$; at the two endpoints, hold with probability $\tfrac12$ and step inward with probability $\tfrac12$ — the model chain for a deterministic-drift cutoff.
--
--   **Lamplighter chains.** Over a graph $G$, the lamplighter state is a pair (lamp configuration in $\{0,1\}^{V}$, lamplighter position in $V$). One step: randomize the lamp at the current position, move one step of the lazy walk on $G$, randomize the lamp at the new position. Its stationary distribution is the product of uniform lamps with the lazy walk's stationary distribution $\deg(v)/2|E|$.
--
--   **Conventions.** The floors $\lfloor\cdot\rfloor$ into $\mathbb N$ clamp negative times to $0$; the mixing-time ratio uses total real division (junk $0$ when the denominator vanishes — degenerate families simply fail to have a cutoff); the limits in $n$ and in the window parameter $\alpha$ are `Filter` limits with `liminf`/`limsup` exactly as displayed.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Ch. 18, Sections 18.1-18.2 and 18.4; Ch. 19, Section 19.1; pp. 247-249, 253-254, 257-258

import Definitions.Def_mm_stopping
import Definitions.Def_mm_lower
import Definitions.Def_mm_spectral
import Definitions.Def_mm_network

/-!
The cutoff phenomenon (Ch. 18) and lamplighter walks (Ch. 19), following
Levin–Peres–Wilmer, *Markov Chains and Mixing Times*.

A *family* of chains is a sequence `P n` on state spaces `V n`; cutoff says
the total variation distance falls from `1` to `0` in a time window that is
asymptotically negligible compared to the mixing time.
-/

namespace MarkovMixing

noncomputable section

open scoped BigOperators

/-- A sequence of chains has a **cutoff** (LPW §18.1, Eq. (18.3)):
`t_mix^{(n)}(ε) / t_mix^{(n)}(1−ε) → 1` for every `ε`. -/
def HasCutoff {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 →
    Filter.Tendsto
      (fun n => (mixingTime (P n) (π n) ε : ℝ) /
        (mixingTime (P n) (π n) (1 - ε) : ℝ))
      Filter.atTop (nhds 1)

/-- A sequence of chains has a **cutoff at `t n` with window `w n`**
(LPW §18.1): `w = o(t)`, and on the time scale `t n + α w n` the distance
tends to `1` as `α → −∞` and to `0` as `α → +∞`. -/
def HasCutoffWindow {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ) (t w : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n => w n / t n) Filter.atTop (nhds 0) ∧
  Filter.Tendsto
    (fun α : ℝ => Filter.liminf
      (fun n => distStationary (P n) (π n) ⌊t n + α * w n⌋₊) Filter.atTop)
    Filter.atBot (nhds 1) ∧
  Filter.Tendsto
    (fun α : ℝ => Filter.limsup
      (fun n => distStationary (P n) (π n) ⌊t n + α * w n⌋₊) Filter.atTop)
    Filter.atTop (nhds 0)

/-- `s(t) = max_x s_x(t)`, the maximal separation distance (LPW §6.4,
Eq. (6.8)). -/
def sepSup {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) : ℝ :=
  ⨆ x : V, sepDist P π x t

/-- A sequence of chains has a **separation cutoff at `t n` with window
`w n`** (LPW §18.4). -/
def HasSepCutoffWindow {V : ℕ → Type*} [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (P : ∀ n, Matrix (V n) (V n) ℝ) (π : ∀ n, V n → ℝ) (t w : ℕ → ℝ) : Prop :=
  Filter.Tendsto (fun n => w n / t n) Filter.atTop (nhds 0) ∧
  Filter.Tendsto
    (fun α : ℝ => Filter.liminf
      (fun n => sepSup (P n) (π n) ⌊t n + α * w n⌋₊) Filter.atTop)
    Filter.atBot (nhds 1) ∧
  Filter.Tendsto
    (fun α : ℝ => Filter.limsup
      (fun n => sepSup (P n) (π n) ⌊t n + α * w n⌋₊) Filter.atTop)
    Filter.atTop (nhds 0)

/-- The lazy biased random walk on the segment `{0, 1, …, n}` with
up-probability `p` (LPW §18.2.1): from an interior vertex, hold with
probability `1/2`, move up with probability `p/2`, down with probability
`(1−p)/2`; from an endpoint, hold with probability `1/2` and move to the
adjacent interior vertex with probability `1/2`. -/
def biasedSegmentWalk (n : ℕ) (p : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k l =>
    if k = 0 then (if l = k then 1 / 2 else if l.val = 1 then 1 / 2 else 0)
    else if k = Fin.last n then
      (if l = k then 1 / 2 else if l.val + 1 = n then 1 / 2 else 0)
    else if l = k then 1 / 2
    else if l.val = k.val + 1 then p / 2
    else if l.val + 1 = k.val then (1 - p) / 2
    else 0

variable {Vv : Type*} [Fintype Vv] [DecidableEq Vv]

/-- The **lamplighter chain** `Υ` on `G⁎ = {0,1}^V × V` (LPW §19.1): with
`P` the lazy simple random walk on `G`, the current lamp is randomized, the
lamplighter moves one `P`-step, and the new lamp is randomized. -/
def lamplighter (G : SimpleGraph Vv) [DecidableRel G.Adj] :
    Matrix ((Vv → Bool) × Vv) ((Vv → Bool) × Vv) ℝ :=
  fun s t =>
    if s.2 = t.2 then
      (if ∀ u : Vv, u ≠ s.2 → t.1 u = s.1 u then
        lazy (graphWalk G) s.2 s.2 / 2
      else 0)
    else if ∀ u : Vv, u ≠ s.2 → u ≠ t.2 → t.1 u = s.1 u then
      lazy (graphWalk G) s.2 t.2 / 4
    else 0

/-- The stationary distribution `π⋆` of the lamplighter chain: uniform lamp
configurations, and the walk's stationary distribution
`π(v) = deg(v)/2|E|` for the position (LPW §19.1). -/
def lamplighterStationary (G : SimpleGraph Vv) [DecidableRel G.Adj] :
    (Vv → Bool) × Vv → ℝ :=
  fun s => (2 ^ Fintype.card Vv : ℝ)⁻¹ *
    ((G.degree s.2 : ℝ) / (2 * G.edgeFinset.card))

end

end MarkovMixing


