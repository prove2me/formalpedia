-- Prove2me | Theorems.Thm_TraceOrder_quintic_eleven_iff
-- name    : TraceOrder.quintic_eleven_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:05:51.950225+00:00
-- url     : https://prove2.me/theorems/b3a0114f-b40d-4f6c-bd11-af506228281d
-- title:
--   Conductor 11.
-- statement:
--   **Conductor 11.**  For a prime `p ≠ 11` the quintic
--   `X⁵ + X⁴ − 4X³ − 3X² + 3X + 1` — the minimal polynomial of `ζ₁₁ + ζ₁₁⁻¹`,
--   defining the cyclic quintic field of conductor `11` — has a root modulo `p`
--   exactly when `p ≡ ±1 (mod 11)`.
--
--   The proof is the conductor-7 argument verbatim with a different pair of
--   factorisations, `A₁₁ = Ψ·Ψ⁻` and `A₁₀ + 1 = Ψ·S`, together with the Bézout
--   identity `(2t − t³)·Ψ⁻ + (1 − 3t² + t⁴)·S = 1` over `ℤ[t]`, which shows that the
--   two spurious branches are coprime with *no* exceptional prime.
--
--   ```lean
--   theorem TraceOrder.quintic_eleven_iff(hp11 : p ≠ 11) :
--       (∃ x : ZMod p, x ^ 5 + x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 + 3 * x + 1 = 0) ↔
--         ((p : ZMod 11) = 1 ∨ (p : ZMod 11) = 10) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/CyclicCubicTypeChannel/TraceOrder.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/CyclicCubicTypeChannel/TraceOrder.lean#L437

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










/-! ## Explicit Chebyshev coefficients -/


variable {R : Type*} [CommRing R]








/-! ## Reading the criterion as a congruence -/





variable (p : ℕ) [hp : Fact p.Prime]


/-! ## Conductor 5: the golden-ratio criterion -/


/-! ## Conductor 7: an independent proof of the cyclic-cubic splitting law -/


/-! ## Conductor 11: the quintic criterion -/

theorem TraceOrder.quintic_eleven_iff(hp11 : p ≠ 11) :
    (∃ x : ZMod p, x ^ 5 + x ^ 4 - 4 * x ^ 3 - 3 * x ^ 2 + 3 * x + 1 = 0) ↔
      ((p : ZMod 11) = 1 ∨ (p : ZMod 11) = 10) := by sorry
