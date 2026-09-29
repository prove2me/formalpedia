-- Prove2me | solution 1 for Round7ZDG.wing_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:15.073979+00:00
-- url     : https://prove2.me/submissions/bb59766e-63a1-4800-b49b-5f65482d68d7

-- Sol generated from Tropical/Round7ZeroDivisorGraph.lean
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



theorem mem_wing {d N x : ℕ} : x ∈ wing d N ↔ (0 < x ∧ x < N) ∧ d ∣ x := by
  simp [wing, Finset.mem_filter, Finset.mem_Ioo, and_assoc]


variable {p q : ℕ}



/-! ## 2. Wing sizes and the vertex count -/




/-! ## 3. The graph is complete bipartite -/




/-! ## 4. From the structural witness back to the numeric trace -/



/-! ## 5. The noise floor for atomic uniform primitives -/







/-! ## 6. Tropical (min-plus) coordinates: the corner at `√N`

In logarithmic coordinates the divisor hyperbola `x · y = N` becomes the
tropical line `X ⊙ Y = log N`; the corner of the line sits at `log N / 2`.
The following two statements record that a divisor pair of a semiprime always
straddles the corner, which is the geometric content of the `√N` floor. -/

open Tropical





open Round7ZDG in
theorem solution(hp : 0 < p) : wing p (p * q) = (Finset.Ioo 0 q).image (p * ·) := by
  ext x
  simp only [mem_wing, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨⟨hx0, hxN⟩, k, rfl⟩
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at hx0
      · exact hk
    · exact lt_of_mul_lt_mul_left hxN (Nat.zero_le p)
  · rintro ⟨k, ⟨hk0, hkq⟩, rfl⟩
    exact ⟨⟨Nat.mul_pos hp hk0, by nlinarith⟩, ⟨k, rfl⟩⟩
