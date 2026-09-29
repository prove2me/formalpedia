-- Prove2me | solution 1 for Round7ZDG.vertices_eq_wing_union
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:27:14.479984+00:00
-- url     : https://prove2.me/submissions/8ccd5a71-8d34-4d8f-8420-094d267576e2

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

theorem mem_vertices {N x : ℕ} :
    x ∈ vertices N ↔ (0 < x ∧ x < N) ∧ ¬ Nat.Coprime x N := by
  simp [vertices, Finset.mem_filter, Finset.mem_Ioo, and_assoc]

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
theorem solution(hp : p.Prime) (hq : q.Prime) :
    vertices (p * q) = wing p (p * q) ∪ wing q (p * q) := by
  ext x
  simp only [mem_vertices, Finset.mem_union, mem_wing]
  constructor
  · rintro ⟨hx, hcop⟩
    have hg : Nat.gcd x (p * q) ≠ 1 := hcop
    -- some prime divides the gcd
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hg
    have hrx : r ∣ x := hrdvd.trans (Nat.gcd_dvd_left _ _)
    have hrN : r ∣ p * q := hrdvd.trans (Nat.gcd_dvd_right _ _)
    rcases (Nat.Prime.dvd_mul hr).mp hrN with h | h
    · left
      exact ⟨hx, ((Nat.prime_dvd_prime_iff_eq hr hp).mp h) ▸ hrx⟩
    · right
      exact ⟨hx, ((Nat.prime_dvd_prime_iff_eq hr hq).mp h) ▸ hrx⟩
  · rintro (⟨hx, hd⟩ | ⟨hx, hd⟩)
    · refine ⟨hx, ?_⟩
      intro hcop
      have : p ∣ Nat.gcd x (p * q) := Nat.dvd_gcd hd ⟨q, rfl⟩
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · refine ⟨hx, ?_⟩
      intro hcop
      have : q ∣ Nat.gcd x (p * q) := Nat.dvd_gcd hd ⟨p, mul_comm p q⟩
      rw [hcop] at this
      exact hq.one_lt.ne' (Nat.dvd_one.mp this)
