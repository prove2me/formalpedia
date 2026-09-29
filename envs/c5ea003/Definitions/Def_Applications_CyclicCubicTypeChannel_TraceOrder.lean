-- Prove2me | Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder
-- name    : Applications_CyclicCubicTypeChannel_TraceOrder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:41:49.398092+00:00
-- url     : https://prove2.me/theorems/45097c08-5686-4f6f-9406-dbb19c2406c3
-- title:
--   Aether Catalog definitions — Applications_CyclicCubicTypeChannel_TraceOrder
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CyclicCubicTypeChannel.TraceOrder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CyclicCubicTypeChannel/TraceOrder.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
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

namespace TraceOrder

/-! ## Chebyshev-type coefficients -/

/-- `A₀ = 0`, `A₁ = 1`, `A_{n+2} = t·A_{n+1} − A_n`. -/
def chebA {R : Type*} [CommRing R] (t : R) : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => t * chebA t (n + 1) - chebA t n


variable {R : Type*} [CommRing R]


/-! ## The companion matrix -/

variable (R) in
/-- The companion matrix of `Y² − tY + 1`. -/
def comp (t : R) : Matrix (Fin 2) (Fin 2) R := !![t, -1; 1, 0]






/-! ## Transfer from an arbitrary matrix to a companion matrix -/

section Field

variable {K : Type*} [Field K]


end Field

/-! ## The order criterion over `𝔽_p` -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]








end Prime


/-! ## Explicit Chebyshev coefficients -/

section Values

variable {R : Type*} [CommRing R]







end Values

/-! ## Reading the criterion as a congruence -/




section Congruence

variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/


end Congruence

end TraceOrder


