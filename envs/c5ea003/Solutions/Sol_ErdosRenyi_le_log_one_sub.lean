-- Prove2me | solution 1 for ErdosRenyi.le_log_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:25:26.419052+00:00
-- url     : https://prove2.me/submissions/4681830c-de81-4fed-99d0-8f1e72e850ec

-- Sol generated from Probability/NumberTheory/ErdosRenyiThreshold.lean
import Mathlib
import Definitions.Def_Probability_NumberTheory_ErdosRenyiThreshold
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

  9.  `card_incident`, `mass_compl`, `prob_avoids_subset`, `Expect_indicator`
                                              -- absence form of independence
  10. `prob_isolated_vertex`, `expected_isolated_count`
                                              -- `E[#isolated vertices] = n (1-p)^{n-1}`
  11. `tendsto_expected_isolated`, `tendsto_expected_isolatedCount`
                                              -- the `e^{-c}` first–moment law at the
                                                 connectivity threshold

  The two deepest asymptotic results — the sharp connectivity threshold with its
  Poisson `e^{-e^{-c}}` limit, and the birth of the giant component — require
  substantial probabilistic machinery (a Poisson limit theorem for the isolated–vertex
  count and a branching–process coupling) that is not currently available in Mathlib.
  This file contains **no unproved statements**: those three theorems are preserved
  verbatim as commented-out statements at the point where they belong, and are listed as
  open formalization targets in the "Open questions" section at the end of the file.
  What *is* proved here is the entire first-moment half of the connectivity threshold:
  the expected number of isolated vertices at `p_n = (log n + c)/n` is computed exactly
  and shown to converge to `e^{-c}`, the mean of the conjectural Poisson limit.
-/

open Finset BigOperators Filter Topology
open scoped Classical

open ErdosRenyi

/-! ## 1.  The `G(n,p)` distribution -/

variable {α : Type*} [Fintype α] [DecidableEq α]






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



/-
The expectation of the indicator of the event "`T` is contained" equals `p^{|T|}`
(the `Expect`/`Prob` translation of `prob_contains_subset`).
-/


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



/-! ### 7.1  The first moment of the isolated–vertex count

The proof of the connectivity threshold splits into a first–moment part (the expected
number of isolated vertices) and a Poisson-limit part.  The first-moment part is
carried out here in full: we compute the exact probability that a fixed vertex is
isolated, deduce the expected number of isolated vertices, and prove that at the
critical density `p_n = (log n + c)/n` this expectation converges to `e^{-c}` — the
mean of the limiting Poisson law. -/









/-! ### 7.2  The `e^{-c}` limit of the expected isolated–vertex count -/






-- The following classical theorem is *stated* but not proved here: its proof needs a
-- Poisson convergence theorem (method of moments / Stein–Chen) for the isolated–vertex
-- count, which is not available in Mathlib.  Rather than leave an unproved `sorry` in the
-- development, the statement is preserved verbatim as a comment and recorded in the
-- "Open questions" section below; the first–moment half of its proof is available above
-- as `tendsto_expected_isolatedCount`.
/-
/-- **Sharp connectivity threshold (Poisson limit).**  For `p_n = (log n + c)/n`, the
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
theorem connectivity_threshold (c : ℝ) :
    Tendsto
      (fun n : ℕ => Prob ((Real.log n + c) / n)
        (Finset.univ.filter (fun s : Finset (Edge n) => (graphOf s).Connected)))
      atTop (𝓝 (Real.exp (-(Real.exp (-c))))) := by
  sorry
-/

/-! ## 8.  The giant component

For `p = (1 + ε)/n` with `ε > 0` fixed (the supercritical regime), the largest
connected component has size `Θ(n)` with high probability, whereas for `p = (1 - ε)/n`
(subcritical) every component has size `O(log n)`.  The standard proof couples the
component-exploration process with a Galton–Watson branching process of mean
`np = 1 ± ε`, and uses a first–moment bound on the number of large components. -/


-- The two giant-component theorems below are likewise *stated* but not proved: they rest
-- on Galton–Watson survival theory and an exploration-process coupling, neither of which
-- is available in Mathlib.  Their statements are preserved verbatim as comments and listed
-- in the "Open questions" section.
/-
/-- **Supercritical giant component.**  For `p = (1 + ε)/n` with `ε > 0`, there is a
constant `β > 0` such that, with probability tending to `1`, the largest component has
size at least `β · n` — i.e. a *giant* component of linear size emerges.

*Proof idea.*  The exploration of a component from a fixed vertex dominates a
`Galton–Watson(Binomial(n-1, p))` process whose mean `np = 1 + ε > 1` is supercritical;
such a process survives with positive probability `ρ = ρ(ε) > 0`.  A second–moment
argument shows the number of vertices in "large" components concentrates around `ρ n`,
producing a unique component of size `Θ(n)`.  The branching-process survival theory and
the concentration step are not yet available in Mathlib. -/
theorem giant_component_supercritical {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 < β ∧
      Tendsto
        (fun n : ℕ => Prob ((1 + ε) / n)
          (Finset.univ.filter
            (fun s : Finset (Edge n) => (β * n : ℝ) ≤ largestComponent s)))
        atTop (𝓝 1) := by
  sorry
-/

/-
/-- **Subcritical regime: no giant component.**  For `p = (1 - ε)/n` with `0 < ε < 1`,
there is a constant `A` such that, with probability tending to `1`, *every* component
has size at most `A · log n`; in particular the largest component is `O(log n)`.

*Proof idea.*  Now the exploration process is dominated by a *subcritical*
`Galton–Watson` process (mean `np = 1 - ε < 1`), which dies out quickly: the
probability that a fixed vertex lies in a component of size `≥ k` decays exponentially
in `k`.  A first–moment (union) bound (`first_moment_threshold`) over all vertices then
shows no component exceeds `A log n`.  This again rests on quantitative
branching-process tail bounds not yet in Mathlib. -/
theorem giant_component_subcritical {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ A : ℝ, 0 < A ∧
      Tendsto
        (fun n : ℕ => Prob ((1 - ε) / n)
          (Finset.univ.filter
            (fun s : Finset (Edge n) => (largestComponent s : ℝ) ≤ A * Real.log n)))
        atTop (𝓝 1) := by
  sorry
-/

/-! ## Open questions

The following are natural extensions of the results above that remain open *as Lean
formalizations* (the underlying mathematics is classical):

* **Poisson limit for the isolated–vertex count.**  The commented-out statement
  `connectivity_threshold` reduces to showing that the number of isolated vertices of
  `G(n, (log n + c)/n)` converges in distribution to `Poisson(e^{-c})`.  Its *first
  moment* is proved above (`tendsto_expected_isolatedCount`: the expectation converges
  to `e^{-c}`); what is missing is the method-of-moments / Stein–Chen upgrade from the
  moments to the distributional limit.

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


open ErdosRenyi in
theorem solution{a : ℝ} (ha : a ≤ 1 / 2) :
    -a - 2 * a ^ 2 ≤ Real.log (1 - a) := by
  have hpos : (0 : ℝ) < 1 - a := by linarith
  have h : Real.log (1 / (1 - a)) ≤ 1 / (1 - a) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div one_ne_zero (ne_of_gt hpos), Real.log_one, zero_sub] at h
  have hb : 1 / (1 - a) - 1 = a / (1 - a) := by
    field_simp
    ring
  rw [hb] at h
  have h2 : a / (1 - a) ≤ a + 2 * a ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith
