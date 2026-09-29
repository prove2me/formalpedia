-- Prove2me | solution 1 for Catalog.Probability.RenormalizedFactorizationFiniteLevel.euler_factor_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T05:13:23.467113+00:00
-- url     : https://prove2.me/submissions/6a8d1ecb-e31d-4991-98d8-684ba88cbb96

-- Sol generated from Speculative/AutoResearch/RenormalizedFactorizationFiniteLevel.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationFiniteLevel
/-
# Finite-level rigidity index and its Euler factor (Cycle 5)

This file closes conjecture **N2** of `FUTURE_DIRECTIONS.md` for the Conjecture-C thread
(`Catalog/Probability/RenormalizedNormalizedFactorization.lean`,
`Catalog/Probability/RenormalizedFactorizationValuation.lean`,
`Catalog/Probability/RenormalizedFactorizationExact.lean`).

In the valuation setting the fibre of the renormalized-product map over a realizable target is
`n = m - 1` free copies of the valuation-zero group
(`DiscreteVal.card_factorizations`).  Conjecture N2 predicted what happens when one *truncates*
the valuation ring modulo `π ^ D`, i.e. replaces the valuation-zero group by the unit group of a
finite local ring.  Here this is proved:

* `card_fibre` — for **any** commutative group `U` and any target `g`, the fibre of the
  `m = n + 1`-fold product map has exactly `#U ^ n` elements; the zeroth slot is determined and
  the other `n` are free.  (This is the truncated analogue of `card_factorizations`, proved by an
  explicit `Fin.cons` bijection rather than by transport, since a finite ring has no
  uniformizer.)
* `card_fibre_zmod_prime_pow` — at level `D ≥ 1` over `ℤ_p`, i.e. in `(ZMod (p ^ D))ˣ`, the fibre
  has exactly `((p - 1) * p ^ (D - 1)) ^ n` elements, which is the predicted
  `((q₀ - 1) q₀^{D-1})^{m-1}` with residue-field size `q₀ = p`.
* `card_fibre_zmod_succ` — the level-to-level recursion `#fibre_{D+1} = p ^ n · #fibre_D`.
* `euler_factor_identity` — the resulting generating function is rational with denominator
  exactly `1 - p ^ n T`:
  `(1 - p^n T) * ∑_{D < N} #fibre_{D+1} · T^{D+1} = (p-1)^n · T · (1 - (p^n T)^N)`.
  So the rigidity index `n = m - 1` is literally the exponent appearing in the Euler factor.
* `card_fibre_eq_one_iff` / `zmod_finite_rigidity_dichotomy` — the finite-level dichotomy: the
  truncated factorization is unique iff `m = 1` or the truncated unit group is trivial.  The
  second alternative is a genuine corner case that does **not** occur in the valuation setting
  (`(ZMod 2)ˣ` is trivial, so `p = 2, D = 1` is rigid for every `m`); this sharpens N2.

No `sorry`, no `native_decide`, no new axioms.
-/

open Catalog.Probability.RenormalizedFactorizationFiniteLevel

open Finset

/-! ## The truncated fibre -/

variable {U : Type*} [CommGroup U]




/-! ## Level `D` over `ℤ_p`: the predicted count `((q₀ - 1) q₀ ^ (D-1)) ^ (m-1)` -/

variable (p D n : ℕ) [Fact p.Prime]




/-! ## The Euler factor

The counting function `D ↦ #fibre_D = (p-1)^n p^{n(D-1)}` is geometric with ratio `p ^ n`,
so its generating function is rational with denominator `1 - p ^ n T`.  The following identity
states exactly that, in the strong finite-`N` form (no convergence hypotheses are needed). -/

variable {R : Type*} [CommRing R]




/-! ## Level transition maps (first step of conjecture N6)

The finite levels form an inverse system: a factorization can be pushed forward along any
surjective homomorphism, and *every* factorization downstairs lifts.  Applied to the reduction
`(ZMod (p ^ (D+1)))ˣ → (ZMod (p ^ D))ˣ` this says the tower of fibres has surjective transition
maps, which is what makes its inverse limit nonempty. -/


variable {V : Type*} [CommGroup V]





/-! ## Lab notes (cycle 5)

Exhaustive enumeration of `#{f : Fin m → (ZMod N)ˣ | ∏ f = g}` (computed by brute force over the
whole unit group, `g = 1` unless stated):

| `N` | `m = 1` | `m = 2` | `m = 3` | predicted `#U^{m-1}` |
|---|---|---|---|---|
| `3 = 3^1` | `1` | `2` | `4` | `2^{m-1}` |
| `9 = 3^2` | `1` | `6` | `36` | `6^{m-1}` |
| `27 = 3^3` | `1` | `18` | — | `18^{m-1}` |
| `81 = 3^4` | `1` | `54` | — | `54^{m-1}` |
| `4 = 2^2` | `1` | `2` | `4` | `2^{m-1}` |
| `8 = 2^3` | `1` | `4` | `16` | `4^{m-1}` |
| `25 = 5^2` | `1` | `20` | — | `20^{m-1}` |
| `2 = 2^1` | `1` | `1` | `1` | `1^{m-1}` (trivial unit group) |

The target does not matter: for `N = 9`, `m = 2` the fibre over `g = -1` also has `6` elements,
as `card_fibre` (which is uniform in `g`) requires.  The `3`-adic column
`2, 6, 18, 54` has constant ratio `3 = p^{m-1}` at `m = 2`, which is the recursion
`card_fibre_zmod_succ` and the denominator `1 - p^{m-1} T` of `euler_factor_identity`.
The row `N = 2` is the exceptional case isolated in `zmod_two_level_one_rigid`.
-/


open Catalog.Probability.RenormalizedFactorizationFiniteLevel in
theorem solution(N : ℕ) (T : R) :
    (1 - (p : R) ^ n * T) * ∑ D ∈ range N, (((p - 1) * p ^ D : ℕ) ^ n : R) * T ^ (D + 1)
      = (((p : R) - 1) ^ n) * T * (1 - ((p : R) ^ n * T) ^ N) := by
  have hp1 : ((p - 1 : ℕ) : R) = (p : R) - 1 := by
    have : 1 ≤ p := Nat.Prime.one_le Fact.out
    push_cast [Nat.cast_sub this]
    ring
  have hsum : ∑ D ∈ range N, (((p - 1) * p ^ D : ℕ) ^ n : R) * T ^ (D + 1)
      = (((p : R) - 1) ^ n) * T * ∑ D ∈ range N, ((p : R) ^ n * T) ^ D := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun D _ => ?_)
    rw [Nat.cast_mul, Nat.cast_pow, hp1, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm D n]
    ring
  have hg : (1 - ((p : R) ^ n * T)) * ∑ D ∈ range N, ((p : R) ^ n * T) ^ D
      = 1 - ((p : R) ^ n * T) ^ N := mul_neg_geom_sum _ _
  rw [hsum]
  linear_combination ((p : R) - 1) ^ n * T * hg
