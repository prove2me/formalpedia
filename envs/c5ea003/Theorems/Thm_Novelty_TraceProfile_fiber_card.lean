-- Prove2me | Theorems.Thm_Novelty_TraceProfile_fiber_card
-- name    : Novelty.TraceProfile.fiber_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:17:32.71085+00:00
-- url     : https://prove2.me/theorems/11aa1a2a-fc8d-43f3-a104-c1e22c3e1007
-- title:
--   The fibre of `x ↦ x + N/x` over a point of the trace set is `{x₀, N/x₀}`,
-- statement:
--   The fibre of `x ↦ x + N/x` over a point of the trace set is `{x₀, N/x₀}`,
--   hence has two elements unless the discriminant `s² - 4N` vanishes.
--
--   ```lean
--   theorem Novelty.TraceProfile.fiber_card(N s : ZMod q) (hN : N ≠ 0) (hs : s ∈ traceSet N) :
--       ((univ.filter (fun x : ZMod q => x ≠ 0)).filter
--         (fun x => x + N * x⁻¹ = s)).card = if s ^ 2 = 4 * N then 1 else 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TraceProfileTraceSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TraceProfileTraceSet.lean#L136

-- Thm stub generated from Novelty/TraceProfileTraceSet.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileTraceSet
/-
# TRACEPROFILE II — the trace set: exact size and one bit per prime

Phase A research file (Novelty domain), Paper 50 / Experiment 385.

For a finite commutative ring `R` and `N : R` the **trace set** is

`S_R(N) = {x + y : x * y = N}`,

the set of all residues that the trace `s = p + q` of a factorisation of `N` can
possibly take.  The experiment measured `|S_{ZMod m}(N)| = (m+1)/2` for odd primes
`m`, and the *joint law* `|S_{ZMod M#}(N)| / M# = 2^{-ω(M#)}` ("exactly one bit per
prime, additively independent").

This file proves the exact statements.

## Main results

* `mem_traceSet` — the defining membership criterion.
* `card_traceSet_ringEquiv` — the trace set is a ring-isomorphism invariant.
* `traceSet_prod` / `card_traceSet_prod` — the trace set of a product ring is the
  product of the trace sets: **CRT multiplicativity**.
* `card_traceSet_zmod_mul` — the arithmetic CRT form for coprime moduli.
* `card_traceSet_prime` — **the exact size over a prime field**:
  `2 * |S_p(N)| = p + 1` if `N` is a nonzero square mod `p`, and `p - 1` otherwise.
  (This *refines* the experimental reading `(m+1)/2`: the true value is
  `(m + χ(N))/2` with `χ` the quadratic character — a `±1` correction invisible at
  the measured precision, but it is the exact law.)
* `traceNat_primorial` — multiplicativity along a squarefree modulus.
* `traceNat_one_bit_per_prime` — **the joint law**:
  `∏ (p-1) ≤ 2^{ω} * |S_{M}(N)| ≤ ∏ (p+1)` for `M = ∏ p` squarefree odd,
  i.e. the trace set has density `2^{-ω(M)}` up to the `(1 ± 1/p)` corrections.
* `card_traceSet_lt_prime` — the trace really is constrained: over a prime field the
  trace set is a proper subset (about half the residues).
-/


open Novelty.TraceProfile

open Finset

/-! ## The trace set of a finite commutative ring -/

variable {R S : Type*} [CommRing R] [Fintype R] [DecidableEq R]
  [CommRing S] [Fintype S] [DecidableEq S]






/-! ## CRT multiplicativity -/




/-! ## The exact size over a prime field -/


variable {q : ℕ} [hq : Fact (Nat.Prime q)]

theorem Novelty.TraceProfile.fiber_card(N s : ZMod q) (hN : N ≠ 0) (hs : s ∈ traceSet N) :
    ((univ.filter (fun x : ZMod q => x ≠ 0)).filter
      (fun x => x + N * x⁻¹ = s)).card = if s ^ 2 = 4 * N then 1 else 2 := by sorry
