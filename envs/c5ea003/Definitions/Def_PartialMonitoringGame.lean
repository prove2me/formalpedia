-- Prove2me | Definitions.Def_PartialMonitoringGame
-- name    : PartialMonitoringGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-07-30T20:12:33.908669+00:00
-- url     : https://prove2.me/theorems/be1b738f-d89c-420f-b340-34b796c7291a
-- statement:
--   A finite adversarial partial-monitoring game $G = (\mathcal{L}, \Phi)$ with $k$ actions, $d$ outcomes and finite feedback alphabet $\Sigma$: in round $t$ the adversary's (obliviously pre-chosen) outcome is $i_t$, the learner samples $A_t$ from a Markov kernel applied to its (action, signal) history, suffers the unobserved loss $\mathcal{L}_{A_t i_t}$ and observes only $\Phi_{A_t i_t} \in \Sigma$. Includes the interconnection measure on feedback histories, the regret $R_n(\pi, i_{1:n}, G)$, and the minimax regret
--
--   $$R_n^*(G) = \inf_\pi \max_{i_{1:n}} R_n,$$
--
--   together with:
--
--   - the cell decomposition of the outcome simplex;
--   - Pareto-optimal/dominated/duplicate/degenerate actions;
--   - neighbouring actions and their neighbourhoods $N_{ab}$;
--   - the global/local observability conditions of Eq. (37.3) on loss-difference estimability;
--   - the observability constants $v_{glo}, v_{loc}$ of §37.5.
-- source:
--   L&S Ch 37.1-37.4, pp.478-487

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
Lattimore & Szepesvári, *Bandit Algorithms* (CUP 2020), Chapter 37:
finite adversarial partial monitoring.

**The game (§37.1, p.480).** A finite `k`-action, `d`-outcome adversarial
partial monitoring problem is specified by a loss matrix `L ∈ ℝ^{k×d}` and a
feedback matrix `Φ ∈ Σ^{k×d}` over a finite alphabet `Σ` of signals. The
adversary secretly chooses outcomes `i_1, …, i_n ∈ [d]`; in round `t` the
learner chooses an action `A_t ∈ [k]`, suffers the (unobserved) loss
`L (A_t, i_t)` and observes only the signal `σ_t = Φ (A_t, i_t)`.

**The protocol.** A history of `t` completed rounds is the sequence
`(A_1, σ_1), …, (A_t, σ_t)` of (action, signal) pairs — the learner never sees
losses or outcomes, only its own actions and the received signals. A policy is
a family of Markov kernels, one per round, mapping the observed history to a
distribution over the next action (the partial-monitoring analogue of the
canonical bandit policy of §4.6 / `Def_BanditPolicy.lean`). Interconnecting a
policy `π` with the fixed outcome sequence `i` yields the probability measure
`pmMeasure G π n i` on histories of length `n` by the usual snoc-recursion:
round `t` samples `A_t ~ π.select t (history)` and appends
`(A_t, Φ (A_t, i_t))`; all randomness comes from the learner.

**Regret and minimax regret (§37.1 p.480, §37.2 p.483).** The regret of `π`
against the outcome sequence `i_{1:n}` is
`R_n(π, i_{1:n}, G) = max_{a ∈ [k]} E[∑_{t=1}^n (L (A_t, i_t) − L (a, i_t))]`
and the minimax regret is `R_n^*(G) = inf_π max_{i_{1:n}} R_n(π, i_{1:n}, G)`.
Both are encoded with real `⨅`/`⨆`; all suprema/infima involved are over
bounded sets (regret is bounded by `2 n max |L|` and the loss matrix is
finite), so the real (conditionally complete) lattice operations agree with
the book's max/inf. Junk-value conventions in degenerate corners (`k = 0`:
no policies, `⨅ ∅ = 0`; `d = 0`, `n ≥ 1`: no outcome sequences, `⨆ ∅ = 0`)
agree with `R_n^* = 0` there.

**Cell decomposition (§37.2.1, pp.483–484).** Identify the adversary's mixed
choices with the probability simplex `P_{d−1} = stdSimplex ℝ (Fin d)` and let
`ℓ_a = L (a, ·) ∈ ℝ^d` be the loss vector of action `a`. The cell of `a` is
`C_a = {u ∈ P_{d−1} : max_b ⟨ℓ_a − ℓ_b, u⟩ ≤ 0}`, the set of outcome
distributions for which `a` is optimal. An action is *dominated* if
`C_a = ∅`. The *dimension* of a non-dominated action is the dimension of the
affine hull of `C_a` (`affineDim`, the `Module.finrank` of the direction of
the affine span; junk value `0` on `∅`). A non-dominated action is *Pareto
optimal* if it has dimension `d − 1` (encoded subtraction-free as
`affineDim + 1 = d`) and *degenerate* otherwise; actions `a ≠ b` are
*duplicates* if `ℓ_a = ℓ_b`, and a game is *degenerate* if it has degenerate
or duplicate actions (p.484).

**Neighbours (p.484).** Pareto optimal actions `a` and `b` are *neighbours*
if `C_a ∩ C_b` has dimension `d − 2` (encoded: the intersection is nonempty
and `affineDim + 2 = d`; nonemptiness replaces the convention
`dim ∅ = −1`, and `a ≠ b` is automatic). The *neighbourhood*
`N_{ab} = {c ∈ [k] : C_a ∩ C_b ⊆ C_c}` is the set of actions incident to the
edge `(a, b)`.

**Observability (§37.2.2, Eq. (37.3), p.486).** A pair of neighbours `a, b`
is *globally observable* if there is an estimation function
`f : [k] × Σ → ℝ` with `∑_{c=1}^k f (c, Φ (c, i)) = L (a, i) − L (b, i)` for
all outcomes `i ∈ [d]`, and *locally observable* if `f` can moreover be
chosen with `f (c, σ) = 0` whenever `c ∉ N_{ab}`. A game is globally/locally
observable if all pairs of neighbouring actions are.

**Observability constants (§37.5, p.496).**
`v_glo = max_{e ∈ E} min_{f ∈ E_e^glo} ‖f‖_∞` and
`v_loc = max_{e ∈ E} min_{f ∈ E_e^loc} ‖f‖_∞`, where the max is over the
edges of the neighbourhood graph and `‖f‖_∞ = max_{c,σ} |f (c, σ)|`. Encoded
with `sSup`/`sInf` (the outer set is finite, the inner min is attained;
`sSup ∅ = sInf ∅ = 0` junk values only arise when the game has no
neighbouring/observable pairs, where the constants are never used).
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- A finite adversarial partial monitoring game `G = (L, Φ)` with `k`
actions, `d` outcomes and signal alphabet `𝕊` (L&S §37.1, p.480): choosing
action `a` when the outcome is `i` incurs the loss `L a i` while the learner
observes only the signal `Φ a i`. -/
structure PartialMonitoringGame (k d : ℕ) (𝕊 : Type*) where
  /-- The loss matrix: `L a i` is the loss of action `a` on outcome `i`. -/
  L : Fin k → Fin d → ℝ
  /-- The feedback matrix: `Φ a i` is the signal the learner observes when
  playing action `a` on outcome `i`. -/
  Φ : Fin k → Fin d → 𝕊

/-- A history of `t` completed partial-monitoring rounds: the sequence
`(A_1, σ_1), …, (A_t, σ_t)` of (action, signal) pairs. The learner observes
neither the losses nor the outcomes — only the feedback signals. -/
abbrev PMHistory (k : ℕ) (𝕊 : Type*) (t : ℕ) := Fin t → Fin k × 𝕊

/-- A partial-monitoring policy: for each round, a Markov kernel from the
observed (action, signal) history to a distribution over the action played
next (the analogue for partial monitoring of the canonical bandit policy of
L&S §4.6). -/
structure PMPolicy (k : ℕ) (𝕊 : Type*) [MeasurableSpace 𝕊] where
  /-- The conditional distribution of the action played in round `t + 1`
  given the history of the first `t` rounds. -/
  select : (t : ℕ) → Kernel (PMHistory k 𝕊 t) (Fin k)
  /-- Each round's selection kernel is a Markov kernel. -/
  markov : ∀ t, IsMarkovKernel (select t)

attribute [instance] PMPolicy.markov

variable {k d : ℕ} {𝕊 : Type*}

/-- One round of the partial-monitoring interconnection when the adversary's
outcome for this round is `j`: given the history of the first `t` rounds,
sample the action `A ~ π.select t` and return the pair `(A, Φ A j)` — the
signal is the deterministic feedback-matrix entry (L&S §37.1). -/
noncomputable def pmStepKernel [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊)
    (π : PMPolicy k 𝕊) (j : Fin d) (t : ℕ) :
    Kernel (PMHistory k 𝕊 t) (Fin k × 𝕊) :=
  (π.select t).map (fun a ↦ (a, G.Φ a j))

instance pmStepKernel.instIsMarkovKernel [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊) (j : Fin d) (t : ℕ) :
    IsMarkovKernel (pmStepKernel G π j t) :=
  Kernel.IsMarkovKernel.map _ (measurable_of_countable _)

/-- Appending one round to a partial-monitoring history is measurable. -/
lemma measurable_pmHistorySnoc [MeasurableSpace 𝕊] {t : ℕ} :
    Measurable (fun p : PMHistory k 𝕊 t × (Fin k × 𝕊) ↦
      Fin.snoc (α := fun _ ↦ Fin k × 𝕊) p.1 p.2) := by
  rw [measurable_pi_iff]
  intro s
  by_cases hs : (s : ℕ) < t
  · have : (fun p : PMHistory k 𝕊 t × (Fin k × 𝕊) ↦
        Fin.snoc (α := fun _ ↦ Fin k × 𝕊) p.1 p.2 s) =
        fun p ↦ p.1 (Fin.castLT s hs) := by
      funext p
      simp [Fin.snoc, hs]
    rw [this]
    exact (measurable_pi_apply _).comp measurable_fst
  · have : (fun p : PMHistory k 𝕊 t × (Fin k × 𝕊) ↦
        Fin.snoc (α := fun _ ↦ Fin k × 𝕊) p.1 p.2 s) =
        fun p ↦ p.2 := by
      funext p
      simp [Fin.snoc, hs]
    rw [this]
    exact measurable_snd

/-- The canonical partial-monitoring probability measure (L&S §37.1): the
distribution of the history after `n` rounds of the interconnection of the
policy `π` with the game `G` when the adversary has secretly fixed the
outcome sequence `i : Fin n → Fin d` (an oblivious adversary, chosen before
the game starts). Round `t` samples `A_t ~ π.select t (history)` and appends
`(A_t, Φ (A_t, i_t))`; all randomness comes from the learner's action
choices. -/
noncomputable def pmMeasure [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊)
    (π : PMPolicy k 𝕊) : (n : ℕ) → (Fin n → Fin d) → Measure (PMHistory k 𝕊 n)
  | 0, _ => Measure.dirac (fun t ↦ t.elim0)
  | n + 1, i =>
      ((pmMeasure G π n (fun t ↦ i t.castSucc)).compProd
        (pmStepKernel G π (i (Fin.last n)) n)).map
        (fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × 𝕊) p.1 p.2)

theorem pmMeasure_isProbabilityMeasure [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊) :
    ∀ (n : ℕ) (i : Fin n → Fin d), IsProbabilityMeasure (pmMeasure G π n i)
  | 0, _ => by
      rw [pmMeasure]
      exact Measure.dirac.isProbabilityMeasure
  | n + 1, i => by
      rw [pmMeasure]
      haveI := pmMeasure_isProbabilityMeasure G π n (fun t ↦ i t.castSucc)
      exact Measure.isProbabilityMeasure_map measurable_pmHistorySnoc.aemeasurable

instance pmMeasure.instIsProbabilityMeasure [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊) (n : ℕ)
    (i : Fin n → Fin d) : IsProbabilityMeasure (pmMeasure G π n i) :=
  pmMeasure_isProbabilityMeasure G π n i

/-- The expected regret of policy `π` on the game `G` against the outcome
sequence `i_{1:n}` (L&S §37.1, p.480):
`R_n(π, i_{1:n}, G) = max_{a ∈ [k]} E[∑_{t=1}^n (L (A_t, i_t) − L (a, i_t))]`,
the expectation taken over the interconnection measure `pmMeasure G π n i`.
The max over the finitely many actions is encoded as a real `⨆` (junk value
`0` when `k = 0`). -/
noncomputable def pmRegret [MeasurableSpace 𝕊] (G : PartialMonitoringGame k d 𝕊)
    (π : PMPolicy k 𝕊) (n : ℕ) (i : Fin n → Fin d) : ℝ :=
  ⨆ a : Fin k, ∫ h, (∑ t, (G.L (h t).1 (i t) - G.L a (i t))) ∂(pmMeasure G π n i)

/-- The minimax regret of the partial monitoring game `G` at horizon `n`
(L&S §37.2, p.483): `R_n^*(G) = inf_π max_{i_{1:n}} R_n(π, i_{1:n}, G)`, the
infimum over all policies of the worst-case regret over all outcome
sequences. Encoded with real `⨅`/`⨆`: for fixed `G` and `n` all regrets lie
in the bounded interval `[−2 n max |L|, 2 n max |L|]`, so the conditionally
complete lattice operations realize the book's inf/max (junk conventions:
`⨅ ∅ = ⨆ ∅ = 0` in the degenerate cases `k = 0` or `d = 0`, which agree with
`R_n^* = 0` there). -/
noncomputable def pmMinimaxRegret [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (n : ℕ) : ℝ :=
  ⨅ π : PMPolicy k 𝕊, ⨆ i : Fin n → Fin d, pmRegret G π n i

/-! ### The geometry of losses and actions (L&S §37.2) -/

/-- The dimension of a subset of `ℝ^d` in the affine sense: the
`Module.finrank` of the direction of its affine span. Junk value `0` for
`∅` (the book's convention is `dim ∅ = −1`; predicates below always pair
`affineDim` with nonemptiness, avoiding both this junk value and natural
subtraction). -/
noncomputable def affineDim {d : ℕ} (s : Set (Fin d → ℝ)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ s).direction

/-- The cell of action `a` (L&S §37.2.1, p.483): the convex polytope of
outcome distributions `u ∈ P_{d−1}` for which `a` is optimal in hindsight,
`C_a = {u ∈ P_{d−1} : max_{b ∈ [k]} ⟨ℓ_a − ℓ_b, u⟩ ≤ 0}` where `ℓ_a` is the
`a`-th row of the loss matrix. -/
def pmCell (G : PartialMonitoringGame k d 𝕊) (a : Fin k) : Set (Fin d → ℝ) :=
  {u ∈ stdSimplex ℝ (Fin d) | ∀ b : Fin k, ∑ i, (G.L a i - G.L b i) * u i ≤ 0}

/-- An action is dominated (L&S p.483) if its cell is empty: it is never
optimal, no matter how the adversary plays. -/
def DominatedAction (G : PartialMonitoringGame k d 𝕊) (a : Fin k) : Prop :=
  pmCell G a = ∅

/-- A non-dominated action is Pareto optimal (L&S p.483) if its cell has
affine dimension `d − 1` (full dimension in the simplex), encoded
subtraction-free as `affineDim (C_a) + 1 = d`. -/
def ParetoOptimalAction (G : PartialMonitoringGame k d 𝕊) (a : Fin k) : Prop :=
  (pmCell G a).Nonempty ∧ affineDim (pmCell G a) + 1 = d

/-- A non-dominated action is degenerate (L&S pp.483–484) if it is not
Pareto optimal: its cell is nonempty but of affine dimension `< d − 1`. -/
def DegenerateAction (G : PartialMonitoringGame k d 𝕊) (a : Fin k) : Prop :=
  (pmCell G a).Nonempty ∧ affineDim (pmCell G a) + 1 ≠ d

/-- Distinct actions `a` and `b` are duplicates (L&S p.484) if they have
identical loss vectors, `ℓ_a = ℓ_b`. -/
def DuplicateActions (G : PartialMonitoringGame k d 𝕊) (a b : Fin k) : Prop :=
  a ≠ b ∧ ∀ i : Fin d, G.L a i = G.L b i

/-- A partial monitoring game is degenerate (L&S p.484) if it has any
degenerate or duplicate actions. -/
def DegenerateGame (G : PartialMonitoringGame k d 𝕊) : Prop :=
  (∃ a, DegenerateAction G a) ∨ ∃ a b, DuplicateActions G a b

/-- Pareto optimal actions `a` and `b` are neighbours (L&S p.484) if
`C_a ∩ C_b` has affine dimension `d − 2`, encoded subtraction-free as: the
intersection is nonempty and `affineDim (C_a ∩ C_b) + 2 = d` (nonemptiness
replaces the convention `dim ∅ = −1`; `a ≠ b` is automatic because the cell
of a Pareto optimal action has dimension `d − 1 ≠ d − 2`, and Pareto optimal
duplicates have `dim (C_a ∩ C_b) = d − 1`, so they are not neighbours). -/
def NeighbouringActions (G : PartialMonitoringGame k d 𝕊) (a b : Fin k) : Prop :=
  ParetoOptimalAction G a ∧ ParetoOptimalAction G b ∧
    (pmCell G a ∩ pmCell G b).Nonempty ∧
    affineDim (pmCell G a ∩ pmCell G b) + 2 = d

/-- `G` has at least one pair of neighbouring actions — the condition
separating trivial games from the rest in the classification theorem
(L&S Theorem 37.11). -/
def HasNeighbouringActions (G : PartialMonitoringGame k d 𝕊) : Prop :=
  ∃ a b, NeighbouringActions G a b

/-- The neighbourhood `N_{ab}` of a pair of neighbouring actions (L&S
p.484): the set of actions incident to the edge `(a, b)` of the
neighbourhood graph, `N_{ab} = {c ∈ [k] : C_a ∩ C_b ⊆ C_c}`. -/
def pmNeighbourhood (G : PartialMonitoringGame k d 𝕊) (a b : Fin k) :
    Set (Fin k) :=
  {c | pmCell G a ∩ pmCell G b ⊆ pmCell G c}

/-! ### Estimating loss differences: global and local observability
(L&S §37.2.2) -/

/-- `f` is an unbiased loss-difference estimation function for the pair
`(a, b)` (L&S Eq. (37.3), p.486): `∑_{c=1}^k f (c, Φ (c, i)) = L (a, i) −
L (b, i)` for every outcome `i ∈ [d]` — precisely the condition under which
`f (A, σ) / p_A` is an unbiased estimator of the loss difference regardless
of the adversary's choice. The set of such `f` is the book's `E_{ab}^glo`. -/
def IsGlobalLossEstimator (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (f : Fin k × 𝕊 → ℝ) : Prop :=
  ∀ i : Fin d, ∑ c : Fin k, f (c, G.Φ c i) = G.L a i - G.L b i

/-- `f` is a local loss-difference estimation function for the pair `(a, b)`
(L&S p.486): it satisfies Eq. (37.3) and moreover `f (c, σ) = 0` whenever
`c ∉ N_{ab}` — only actions incident to the edge are used for estimation.
The set of such `f` is the book's `E_{ab}^loc`. -/
def IsLocalLossEstimator (G : PartialMonitoringGame k d 𝕊) (a b : Fin k)
    (f : Fin k × 𝕊 → ℝ) : Prop :=
  IsGlobalLossEstimator G a b f ∧
    ∀ c : Fin k, c ∉ pmNeighbourhood G a b → ∀ σ : 𝕊, f (c, σ) = 0

/-- A partial monitoring game is globally observable (L&S p.486) if every
pair of neighbouring actions admits an unbiased loss-difference estimation
function. -/
def GloballyObservable (G : PartialMonitoringGame k d 𝕊) : Prop :=
  ∀ a b : Fin k, NeighbouringActions G a b → ∃ f, IsGlobalLossEstimator G a b f

/-- A partial monitoring game is locally observable (L&S p.486) if every
pair of neighbouring actions admits an unbiased loss-difference estimation
function supported on the neighbourhood `N_{ab}`. Local observability
implies global observability. -/
def LocallyObservable (G : PartialMonitoringGame k d 𝕊) : Prop :=
  ∀ a b : Fin k, NeighbouringActions G a b → ∃ f, IsLocalLossEstimator G a b f

/-- The sup-norm `‖f‖_∞ = max_{c, σ} |f (c, σ)|` of an estimation function
(junk value `0` when `k = 0`). -/
noncomputable def pmEstimatorNorm [Fintype 𝕊] {k : ℕ} (f : Fin k × 𝕊 → ℝ) : ℝ :=
  ⨆ p : Fin k × 𝕊, |f p|

/-- The global observability constant `v_glo = max_{e ∈ E} min_{f ∈ E_e^glo}
‖f‖_∞` of a game (L&S §37.5, p.496): the worst case over the edges of the
neighbourhood graph of the smallest sup-norm of an unbiased loss-difference
estimation function. Encoded with `sSup`/`sInf`; the outer set is finite and,
for globally observable pairs, the inner infimum is over a nonempty set
bounded below by `0` (junk value `0` for pairs with no estimator and
`sSup ∅ = 0` when there are no neighbouring actions). -/
noncomputable def pmGlobObsConst [Fintype 𝕊] (G : PartialMonitoringGame k d 𝕊) : ℝ :=
  sSup {v : ℝ | ∃ a b : Fin k, NeighbouringActions G a b ∧
    v = sInf {r : ℝ | ∃ f, IsGlobalLossEstimator G a b f ∧ r = pmEstimatorNorm f}}

/-- The local observability constant `v_loc = max_{e ∈ E} min_{f ∈ E_e^loc}
‖f‖_∞` of a game (L&S §37.5, p.496), the analogue of `pmGlobObsConst` with
estimation functions supported on the neighbourhoods `N_{ab}`. This is the
game-dependent constant appearing in the `O(v_loc k^{3/2} √(n log k))` regret
bound for locally observable games (Theorems 37.15–37.17). -/
noncomputable def pmLocObsConst [Fintype 𝕊] (G : PartialMonitoringGame k d 𝕊) : ℝ :=
  sSup {v : ℝ | ∃ a b : Fin k, NeighbouringActions G a b ∧
    v = sInf {r : ℝ | ∃ f, IsLocalLossEstimator G a b f ∧ r = pmEstimatorNorm f}}

end BanditAlgorithm


