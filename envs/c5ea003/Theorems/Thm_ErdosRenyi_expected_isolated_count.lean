-- Prove2me | Theorems.Thm_ErdosRenyi_expected_isolated_count
-- name    : ErdosRenyi.expected_isolated_count
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:20:42.166044+00:00
-- url     : https://prove2.me/theorems/70440679-03d9-4bba-876a-918aa998b519
-- title:
--   Expected number of isolated vertices of `G(n,p)`: `n (1 - p) ^ (n - 1)`.
-- statement:
--   **Expected number of isolated vertices** of `G(n,p)`: `n (1 - p) ^ (n - 1)`.
--   This is linearity of expectation applied to the indicators of the `n` isolation
--   events, each of probability `(1 - p) ^ (n - 1)` by `prob_isolated_vertex`.
--
--   ```lean
--   theorem ErdosRenyi.expected_isolated_count{n : ℕ} (p : ℝ) :
--       Expect p (fun s : Finset (Edge n) => (isolatedCount s : ℝ))
--         = n * (1 - p) ^ (n - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/NumberTheory/ErdosRenyiThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/NumberTheory/ErdosRenyiThreshold.lean#L416

-- Thm stub generated from Probability/NumberTheory/ErdosRenyiThreshold.lean
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

theorem ErdosRenyi.expected_isolated_count{n : ℕ} (p : ℝ) :
    Expect p (fun s : Finset (Edge n) => (isolatedCount s : ℝ))
      = n * (1 - p) ^ (n - 1) := by sorry
