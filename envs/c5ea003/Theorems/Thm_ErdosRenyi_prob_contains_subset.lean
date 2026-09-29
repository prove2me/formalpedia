-- Prove2me | Theorems.Thm_ErdosRenyi_prob_contains_subset
-- name    : ErdosRenyi.prob_contains_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:43.317509+00:00
-- url     : https://prove2.me/theorems/ca2f4b34-6844-442e-84cd-d972a4b10696
-- title:
--   Prob contains subset
-- statement:
--   Formal statement of `ErdosRenyi.prob_contains_subset` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ErdosRenyi.prob_contains_subset(p : ℝ) (T : Finset α) :
--       Prob p (Finset.univ.filter (fun s => T ⊆ s)) = p ^ T.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ErdosRenyiThreshold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ErdosRenyiThreshold.lean#L103

-- Thm stub generated from Applications/ErdosRenyiThreshold.lean
import Mathlib
import Definitions.Def_Applications_ErdosRenyiThreshold
/-
  # Threshold phenomena for the Erdős–Rényi random graph `G(n,p)`

  This file develops, from first principles, the *first–moment* and *second–moment*
  machinery underlying the classical threshold theorems for the Erdős–Rényi random
  graph `G(n,p)`, together with precise descriptions of three headline threshold
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

  The two deepest asymptotic results — the sharp connectivity threshold with its
  Poisson `e^{-e^{-c}}` limit, and the birth of the giant component — are stated
  as open formalization targets.  Their proofs require substantial probabilistic
  machinery (a Poisson limit theorem for the isolated–vertex count and a
  branching–process coupling) that is not currently available in Mathlib; they are
  therefore documented as open formalization targets rather than exported as
  theorems in the "Open questions" section at the end of the file.
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

theorem ErdosRenyi.prob_contains_subset(p : ℝ) (T : Finset α) :
    Prob p (Finset.univ.filter (fun s => T ⊆ s)) = p ^ T.card := by sorry
