-- Prove2me | Theorems.Thm_Round7ZDG_vertices_eq_wing_union
-- name    : Round7ZDG.vertices_eq_wing_union
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:38:01.935292+00:00
-- url     : https://prove2.me/theorems/2ead98da-6941-4219-bc88-555603890715
-- title:
--   A vertex of the zero-divisor graph lies in one of the two wings.
-- statement:
--   A vertex of the zero-divisor graph lies in one of the two wings.
--
--   ```lean
--   theorem Round7ZDG.vertices_eq_wing_union(hp : p.Prime) (hq : q.Prime) :
--       vertices (p * q) = wing p (p * q) ∪ wing q (p * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/Round7ZeroDivisorGraph.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/Round7ZeroDivisorGraph.lean#L63

-- Thm stub generated from Tropical/Round7ZeroDivisorGraph.lean
import Mathlib
import Definitions.Def_Tropical_Round7ZeroDivisorGraph

/-!
# Round-7 closure ZDG + STATICRHO: the zero-divisor graph of a semiprime and the noise floor

This file formalises the arithmetic core of the round-7 closures `ZDG`
(experiment 327: *structural witnesses outside the trace lemma*) and the
refined `noise-floor principle` extracted from `STATICRHO` (experiment 326:
*the principle bounds atomic-uniform primitives*).

Setting: `N = p * q` with `p, q` distinct primes.  We model the zero-divisor
graph `Γ(ℤ/Nℤ)` on the concrete vertex set of nonzero, non-coprime residues
`0 < x < N`, with `x ~ y` iff `N ∣ x * y`.

Main results.

* `vertices_eq_wing_union` / `wings_disjoint` : the vertex set splits into the
  two *wings* (multiples of `p`, multiples of `q`).
* `card_wing`, `card_vertices` : the wings have sizes `q - 1` and `p - 1`, so
  `|V| = p + q - 2`.
* `cross_edge`, `no_intra_edge_p`, `no_intra_edge_q` : the graph is exactly the
  **complete bipartite graph** `K_{q-1, p-1}` — every cross-wing pair is an
  edge, no intra-wing pair is.
* `factor_recovery_trace`, `prime_isRoot_traceQuadratic` : the structural datum
  `|V|` is exactly the trace `p + q` (minus 2), so `p` and `q` are the roots of
  `X² - (|V| + 2) X + N`.  This is the precise sense in which the *structural*
  witness collapses onto the *numeric* trace witness.
* `atomic_uniform_success_le` : the **noise-floor bound for an atomic uniform
  primitive** — a single uniform query `a ← [1, N)` reveals a factor with
  probability `(p + q - 2)/N ≤ 2/p`, i.e. at most `2 / (smallest prime)`.
* `four_le_sq_trace` and `noise_floor_lower` : the density is bounded *below*
  by the balanced (`√N`) noise floor, and the bound is attained only when the
  semiprime is balanced.
* Tropical section: in min-plus (logarithmic) coordinates the divisor hyperbola
  degenerates to the tropical line `X ⊙ Y = N` whose corner sits at `√N`;
  `trop_corner_straddle` and `trop_mul_log_le` record that every divisor pair
  straddles the corner.
-/

open Round7ZDG

open Finset

/-! ## 1. Vertices and wings -/





variable {p q : ℕ}

theorem Round7ZDG.vertices_eq_wing_union(hp : p.Prime) (hq : q.Prime) :
    vertices (p * q) = wing p (p * q) ∪ wing q (p * q) := by sorry
