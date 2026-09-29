-- Prove2me | Theorems.Thm_TraceOrder_exists_companion_order_iff
-- name    : TraceOrder.exists_companion_order_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:05:38.399489+00:00
-- url     : https://prove2.me/theorems/125d00f5-f93b-4a60-9b5c-e0d438d52e92
-- title:
--   Existence of an order-`m` companion matrix over `𝔽_p`, for an odd prime
-- statement:
--   Existence of an order-`m` companion matrix over `𝔽_p`, for an odd prime
--   `m ≠ p`, is exactly the congruence `p ≡ ±1 (mod m)` in the form `m ∣ p² − 1`.
--
--   ```lean
--   theorem TraceOrder.exists_companion_order_iff{m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmp : m ≠ p) :
--       (∃ t : ZMod p, comp (ZMod p) t ^ m = 1 ∧ comp (ZMod p) t ≠ 1) ↔ m ∣ p ^ 2 - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/CyclicCubicTypeChannel/TraceOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/CyclicCubicTypeChannel/TraceOrder.lean#L209

-- Thm stub generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
/-
# The Frobenius trace criterion for an arbitrary conductor

## Context (FACT round-32 #3, cycle 2)

`Applications.CyclicCubicTypeChannel.Splitting` settles conductor `7`: the cubic
`X³ + X² − 2X − 1` has a root mod `p` iff `p ≡ ±1 (mod 7)`.  The proof used one
structural fact — the companion matrix of `Y² − xY + 1` has order `7` exactly
when `x = ζ + ζ⁻¹` — which has nothing to do with `7`.

This file isolates that structure for an arbitrary odd prime conductor `m`,
using the Chebyshev-type coefficient sequence

  `A₀ = 0`, `A₁ = 1`, `A_{n+2}(t) = t·A_{n+1}(t) − A_n(t)`,

which satisfies `M^{n+1} = A_{n+1}(t)·M − A_n(t)·I` for every `2 × 2` matrix of
trace `t` and determinant `1`.  Main results:

* `TraceOrder.pow_eq_cheb` — the closed form for powers;
* `TraceOrder.companion_pow_of_matrix_pow` — *any* order-`m` element of
  `SL₂(𝔽_p)` that is not scalar transfers its order to the companion matrix of
  its trace;
* `TraceOrder.exists_companion_order_iff` — for odd primes `m ≠ p`:
  a companion matrix of order `m` exists over `𝔽_p` **iff** `p ≡ ±1 (mod m)`
  (in the form `m ∣ p² − 1`);
* `TraceOrder.cheb_root_iff` — the polynomial form: the pair
  `(A_m, A_{m−1}) = (0, −1)` is solvable over `𝔽_p` iff `m ∣ p² − 1`;
* `TraceOrder.golden_iff` — conductor `5`: `X² + X − 1` has a root mod `p` iff
  `p ≡ ±1 (mod 5)` (the golden-ratio / Fibonacci criterion);
* `TraceOrder.cubic_seven_iff` — conductor `7`: an independent second proof of
  `CyclicCubic.root_iff`, obtained by specialising the general criterion;
* `TraceOrder.quintic_eleven_iff` — conductor `11`: the quintic
  `X⁵ + X⁴ − 4X³ − 3X² + 3X + 1` (minimal polynomial of `ζ₁₁ + ζ₁₁⁻¹`) has a
  root mod `p` iff `p ≡ ±1 (mod 11)`.
-/

open Matrix

open TraceOrder

/-! ## Chebyshev-type coefficients -/



variable {R : Type*} [CommRing R]


/-! ## The companion matrix -/







/-! ## Transfer from an arbitrary matrix to a companion matrix -/


variable {K : Type*} [Field K]



/-! ## The order criterion over `𝔽_p` -/


variable (p : ℕ) [hp : Fact p.Prime]






set_option maxRecDepth 4000 in

theorem TraceOrder.exists_companion_order_iff{m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2) (hmp : m ≠ p) :
    (∃ t : ZMod p, comp (ZMod p) t ^ m = 1 ∧ comp (ZMod p) t ≠ 1) ↔ m ∣ p ^ 2 - 1 := by sorry
