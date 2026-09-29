-- Prove2me | Definitions.Def_Tropical_Round7ZeroDivisorGraph
-- name    : Tropical_Round7ZeroDivisorGraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:28.758681+00:00
-- url     : https://prove2.me/theorems/c753c722-1b0a-4e85-81b9-9b92e5738bcc
-- title:
--   Aether Catalog definitions — Tropical_Round7ZeroDivisorGraph
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Round7ZeroDivisorGraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Round7ZeroDivisorGraph.lean by skeleton subtraction
import Mathlib

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

namespace Round7ZDG

open Finset

/-! ## 1. Vertices and wings -/

/-- The vertex set of the zero-divisor graph of `ℤ/Nℤ`: the nonzero residues
that are not coprime to `N`. -/
def vertices (N : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 N).filter (fun x => ¬ Nat.Coprime x N)

/-- The *wing* of `d`: the nonzero residues below `N` divisible by `d`. -/
def wing (d N : ℕ) : Finset ℕ :=
  (Finset.Ioo 0 N).filter (fun x => d ∣ x)



variable {p q : ℕ}



/-! ## 2. Wing sizes and the vertex count -/




/-! ## 3. The graph is complete bipartite -/




/-! ## 4. From the structural witness back to the numeric trace -/



/-! ## 5. The noise floor for atomic uniform primitives -/

/-- The success density of a single uniform query: the fraction of residues in
`(0, N)` that expose a factor. -/
noncomputable def hitDensity (p q : ℕ) : ℚ := ((vertices (p * q)).card : ℚ) / (p * q : ℕ)






/-! ## 6. Tropical (min-plus) coordinates: the corner at `√N`

In logarithmic coordinates the divisor hyperbola `x · y = N` becomes the
tropical line `X ⊙ Y = log N`; the corner of the line sits at `log N / 2`.
The following two statements record that a divisor pair of a semiprime always
straddles the corner, which is the geometric content of the `√N` floor. -/

open Tropical




end Round7ZDG


