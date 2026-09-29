-- Prove2me | Definitions.Def_Probability_ErdosRenyiThreshold
-- name    : Probability_ErdosRenyiThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:20.394123+00:00
-- url     : https://prove2.me/theorems/155e8d71-691e-4eab-9c51-35cc31259473
-- title:
--   Aether Catalog definitions — Probability_ErdosRenyiThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ErdosRenyiThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ErdosRenyiThreshold.lean by skeleton subtraction
import Mathlib
/-
  # Threshold phenomena for the Erdős–Rényi random graph `G(n,p)`

  This file develops, from first principles, the *first–moment* and *second–moment*
  machinery underlying the classical threshold theorems for the Erdős–Rényi random
  graph `G(n,p)`, together with faithful statements of the three headline threshold
  results (connectivity, the emergence of the giant component, and the second–moment
  method for subgraph counts).

  ## Design

  We model `G(n,p)` *elementarily* as a finite probability distribution on the type
  of *configurations*.  A configuration is a `Finset α`, where `α` is the finite type
  of *potential edges*; the finset records exactly which edges are present.  Under
  `G(n,p)` each potential edge is included independently with probability `p`, so the
  probability mass of a configuration `s` is

  `mass p s = p ^ |s| * (1 - p) ^ (N - |s|)`,   where `N = |α|`.

  This is a genuine probability distribution: `∑ s, mass p s = 1` (a binomial
  expansion, `ErdosRenyi.total_mass`).  Modelling the law elementarily — rather than
  through `MeasureTheory` — keeps every probability a finite real sum, so the
  independence and linearity computations reduce to clean `Finset` identities.

  ## Dependency structure (no circularity)

  The lemmas are arranged so that each only uses results stated strictly *before* it,
  exactly as required:

  1. `mass_nonneg`, `total_mass`              -- basic facts about the distribution
  2. `prob_contains_subset`                   -- **independence of edge events**
  3. `union_bound`                            -- **standalone union bound**
  4. `expected_count`                         -- **linearity of expectation**
  5. `first_moment_threshold`                 -- uses `union_bound` + `prob_contains_subset`
  6. `prob_eq_zero_le_variance_div_sq`        -- Chebyshev / second–moment inequality
  7. `tendsto_zero_of_variance_bound`         -- analytic squeeze used by ↓
  8. `subgraph_count_pos_whp`                 -- **second–moment method** (uses 6 + 7)

  The two deepest asymptotic results — the Poisson `e^{-e^{-c}}` window form of the
  connectivity threshold, and the birth of the giant component — need substantial
  further probabilistic machinery (a Poisson limit theorem for the isolated–vertex
  count and a branching–process coupling) that is not currently available in Mathlib.
  Their statements are therefore recorded verbatim as *commented* open formalization
  targets, so that this file exports no unproved declaration.

  The *sharp connectivity threshold at* `p = log n / n` (`P(connected) → 0` for
  `p = c·log n/n` with `c < 1`, and `→ 1` for `c > 1`) is proved in the companion files
  `Probability.ErdosRenyiConnectivityLower` and
  `Probability.ErdosRenyiConnectivityUpper`.
-/

open Finset BigOperators Filter Topology
open scoped Classical

namespace ErdosRenyi

/-! ## 1.  The `G(n,p)` distribution -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability mass that `G(n,p)` assigns to the configuration `s : Finset α`
(the set of present edges): the `|s|` present edges each contribute a factor `p`, and
the remaining `N - |s|` absent edges each contribute a factor `1 - p`. -/
noncomputable def mass (p : ℝ) (s : Finset α) : ℝ :=
  p ^ s.card * (1 - p) ^ (Fintype.card α - s.card)

/-- The probability of an event `E`, presented as a finite set of configurations:
the sum of the masses of the configurations in `E`. -/
noncomputable def Prob (p : ℝ) (E : Finset (Finset α)) : ℝ := ∑ s ∈ E, mass p s




/-! ## 2.  Independence of edge events

The basic independence statement: the probability that the random graph contains a
*fixed* set `T` of edges is exactly `p^{|T|}`, irrespective of the other edges.  This
is the engine behind every first–moment computation. -/

/-
**Independence of edge events.**  The probability that `G(n,p)` contains every
edge of a fixed set `T` equals `p ^ |T|`.

The event `{s | T ⊆ s}` is in bijection (via `s ↦ s \ T`, with inverse `R ↦ T ∪ R`)
with the subsets `R` of the complementary edge set `Tᶜ`.  Summing the masses,
`∑_{R ⊆ Tᶜ} p^{|T| + |R|}(1-p)^{|Tᶜ| - |R|} = p^{|T|} (p + (1-p))^{|Tᶜ|} = p^{|T|}`.
-/

/-! ## 3.  The union bound

A completely general, standalone union bound for the finite model: the probability of
a finite union of events is at most the sum of their probabilities. -/

/-
**Union bound.**  For a finite index set `A` and events `ev a`, the probability of
the union `⋃ a ∈ A, ev a` (modelled by `A.biUnion ev`) is at most `∑ a ∈ A, Prob (ev a)`.
The proof only uses nonnegativity of the masses: each configuration in the union is
counted at least once on the right.
-/

/-! ## 4.  Linearity of expectation and the expected subgraph count -/

/-- Expectation of a real random variable `X` (a function on configurations) under
`G(n,p)`. -/
noncomputable def Expect (p : ℝ) (X : Finset α → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Finset α)), mass p s * X s


/-
The expectation of the indicator of the event "`T` is contained" equals `p^{|T|}`
(the `Expect`/`Prob` translation of `prob_contains_subset`).
-/

/-- The number of members of the family `𝒯` that are present in the configuration `s`
(i.e. the number of "copies" realised by `s`). -/
noncomputable def count (𝒯 : Finset (Finset α)) (s : Finset α) : ℕ :=
  (𝒯.filter (fun T => T ⊆ s)).card

/-
**Expected count (linearity of expectation).**  For a family `𝒯` of edge sets, the
expected number of members present equals `∑ T ∈ 𝒯, p^{|T|}`.  This is linearity of
expectation (`Expect_sum`) applied to the sum of indicators, together with
`Expect_indicator_contains`.
-/

/-! ## 5.  The first–moment threshold -/

/-
**First–moment threshold.**  The probability that *some* member of the family `𝒯`
appears is at most the expected count `∑ T ∈ 𝒯, p^{|T|}`.  This is `union_bound`
applied to the events `{s | T ⊆ s}`, evaluated with `prob_contains_subset`.

Consequently, if `∑ T ∈ 𝒯, p^{|T|} → 0` then a.a.s. no copy appears — the standard
first–moment vanishing criterion.
-/

/-! ## 6.  The second–moment method

The variance of a random variable and Chebyshev's inequality, specialised to the
key "second–moment" inequality `P(X = 0) ≤ Var X / (E X)²`. -/

/-- Variance of `X` under `G(n,p)`. -/
noncomputable def Variance (p : ℝ) (X : Finset α → ℝ) : ℝ :=
  Expect p (fun s => (X s - Expect p X) ^ 2)

/-- The probability that `X = 0`. -/
noncomputable def probZero (p : ℝ) (X : Finset α → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ.filter (fun s => X s = 0)), mass p s

/-
**Second–moment inequality (Chebyshev).**  For any `X`,
`P(X = 0) ≤ Var X / (E X)²` (when `E X ≠ 0`).

On the event `{X = 0}` we have `(X - E X)² = (E X)²`, so the variance — a sum of
nonnegative terms — is at least `(E X)² · P(X = 0)`. -/

/-
**Analytic squeeze.**  If a nonnegative sequence `P0 n` is bounded by
`V n / (E n)²`, the means `E n` tend to `+∞`, and the variances satisfy
`V n ≤ C · E n` (i.e. `Var = O(E)`), then `P0 n → 0`.  Indeed
`V n / (E n)² ≤ C / E n → 0`.
-/


/-! ## 7.  The connectivity threshold

We now turn to the graph–theoretic threshold theorems.  For these we instantiate the
potential–edge type as the non-loop pairs of vertices on `Fin n`, and turn a
configuration into an honest `SimpleGraph (Fin n)`.

The connectivity theorem below is the sharp threshold:
for `p = (log n + c)/n`, the probability that `G(n,p)` is connected converges to the
Gumbel/Poisson limit `e^{-e^{-c}}`.  The mechanism is that, at this density, the only
obstruction to connectivity is (a.a.s.) the presence of an isolated vertex, and the
number of isolated vertices is asymptotically `Poisson(e^{-c})`. -/

/-- The type of potential edges of the complete graph on `Fin n`: unordered, non-loop
pairs of vertices. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The simple graph on `Fin n` whose edge set is exactly the configuration `s`. -/
noncomputable def graphOf {n : ℕ} (s : Finset (Edge n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet ((fun e : Edge n => (e : Sym2 (Fin n))) '' (s : Set (Edge n)))

/- **Sharp connectivity threshold (Poisson limit).**  For `p_n = (log n + c)/n`, the
probability that `G(n, p_n)` is connected converges to `e^{-e^{-c}}` as `n → ∞`.

*Proof idea.*  Write `D_n` for the event of disconnection.  A disconnected graph either
has an isolated vertex or splits off a component of size `2 ≤ k ≤ n/2`.  A first–moment
computation (`first_moment_threshold`) shows the expected number of small split-off
components of size `≥ 2` tends to `0`, so disconnection is a.a.s. *caused by an isolated
vertex*.  The number `I_n` of isolated vertices has expectation
`n (1-p_n)^{n-1} → e^{-c}`, and by the method of moments `I_n` converges in
distribution to `Poisson(e^{-c})`; hence `P(I_n = 0) → e^{-e^{-c}}`, giving the claimed
limit for connectivity.

The full proof needs a Poisson convergence theorem for the isolated–vertex count,
which is not yet in Mathlib; we record the statement and leave it open. -/
/- The *Poisson-window* form of the connectivity threshold is recorded here as an open
formalization target (no declaration is exported, so that this file contains no
unproved statements).  The coarser but fully proved *sharp threshold* at
`p = c·log n/n`, `c ≠ 1`, is available in `Probability.ErdosRenyiConnectivityUpper`
as `ErdosRenyi.connectivity_sharp_threshold`.

Proposed declaration:

  theorem connectivity_threshold (c : ℝ) :
      Tendsto
        (fun n : ℕ => Prob ((Real.log n + c) / n)
          (Finset.univ.filter (fun s : Finset (Edge n) => (graphOf s).Connected)))
        atTop (𝓝 (Real.exp (-(Real.exp (-c)))))
-/

/-! ## 8.  The giant component

For `p = (1 + ε)/n` with `ε > 0` fixed (the supercritical regime), the largest
connected component has size `Θ(n)` with high probability, whereas for `p = (1 - ε)/n`
(subcritical) every component has size `O(log n)`.  The standard proof couples the
component-exploration process with a Galton–Watson branching process of mean
`np = 1 ± ε`, and uses a first–moment bound on the number of large components. -/


/- **Supercritical giant component.**  For `p = (1 + ε)/n` with `ε > 0`, there is a
constant `β > 0` such that, with probability tending to `1`, the largest component has
size at least `β · n` — i.e. a *giant* component of linear size emerges.

*Proof idea.*  The exploration of a component from a fixed vertex dominates a
`Galton–Watson(Binomial(n-1, p))` process whose mean `np = 1 + ε > 1` is supercritical;
such a process survives with positive probability `ρ = ρ(ε) > 0`.  A second–moment
argument shows the number of vertices in "large" components concentrates around `ρ n`,
producing a unique component of size `Θ(n)`.  The branching-process survival theory and
the concentration step are not yet available in Mathlib. -/
/- Open formalization target (branching-process coupling not yet available):

  theorem giant_component_supercritical {ε : ℝ} (hε : 0 < ε) :
      ∃ β : ℝ, 0 < β ∧
        Tendsto
          (fun n : ℕ => Prob ((1 + ε) / n)
            (Finset.univ.filter
              (fun s : Finset (Edge n) => (β * n : ℝ) ≤ largestComponent s)))
          atTop (𝓝 1)
-/

/- **Subcritical regime: no giant component.**  For `p = (1 - ε)/n` with `0 < ε < 1`,
there is a constant `A` such that, with probability tending to `1`, *every* component
has size at most `A · log n`; in particular the largest component is `O(log n)`.

*Proof idea.*  Now the exploration process is dominated by a *subcritical*
`Galton–Watson` process (mean `np = 1 - ε < 1`), which dies out quickly: the
probability that a fixed vertex lies in a component of size `≥ k` decays exponentially
in `k`.  A first–moment (union) bound (`first_moment_threshold`) over all vertices then
shows no component exceeds `A log n`.  This again rests on quantitative
branching-process tail bounds not yet in Mathlib. -/
/- Open formalization target (subcritical branching-process tail bounds not yet
available):

  theorem giant_component_subcritical {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
      ∃ A : ℝ, 0 < A ∧
        Tendsto
          (fun n : ℕ => Prob ((1 - ε) / n)
            (Finset.univ.filter
              (fun s : Finset (Edge n) => (largestComponent s : ℝ) ≤ A * Real.log n)))
          atTop (𝓝 1)
-/

/-! ## Open questions

The following are natural extensions of the results above that remain open *as Lean
formalizations* (the underlying mathematics is classical):

* **Poisson limit for the isolated–vertex count.**  The proof of
  `connectivity_threshold` reduces to showing that the number of isolated vertices of
  `G(n, (log n + c)/n)` converges in distribution to `Poisson(e^{-c})`.  A reusable
  method-of-moments / Stein–Chen Poisson convergence theorem in Mathlib would close
  this gap and many like it.

* **Branching-process coupling.**  Both giant-component statements rest on coupling the
  component-exploration process with a Galton–Watson process and on its survival
  probability `ρ(ε)`.  Formalizing Galton–Watson survival/extinction and the coupling
  inequality would make `giant_component_supercritical` and
  `giant_component_subcritical` provable.

* **Uniqueness of the giant component.**  Beyond mere existence of a `Θ(n)` component,
  one expects a *unique* giant component of size `(ρ + o(1)) n` in the supercritical
  regime; formalizing uniqueness is a further step.

* **Sharp threshold for Hamiltonicity.**  At `p = (log n + log log n + c)/n` the graph
  `G(n,p)` is Hamiltonian with probability `→ e^{-e^{-c}}`.  This is a strictly harder
  threshold than connectivity and would be a flagship target.

* **General subgraph thresholds (Bollobás).**  The threshold for the appearance of a
  fixed graph `H` is `n^{-1/m(H)}`, where `m(H)` is the maximum edge density of a
  subgraph of `H`.  The variance estimate feeding `subgraph_count_pos_whp` should be
  assembled into this general statement.
-/

end ErdosRenyi


