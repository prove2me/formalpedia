-- Prove2me | Theorems.Thm_Catalog_Probability_RenormalizedFactorizationFiniteLevel_pushFibre_surjective
-- name    : Catalog.Probability.RenormalizedFactorizationFiniteLevel.pushFibre_surjective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:37:36.671242+00:00
-- url     : https://prove2.me/theorems/2f113876-32ef-4a6b-a7ee-a6c0000f91fc
-- title:
--   Every factorization downstairs lifts.
-- statement:
--   **Every factorization downstairs lifts.**  If `φ` is a surjective homomorphism then the
--   induced map on fibres is surjective: one lifts the `n` free slots arbitrarily and repairs the
--   zeroth slot.
--
--   ```lean
--   theorem Catalog.Probability.RenormalizedFactorizationFiniteLevel.pushFibre_surjective(φ : U →* V) (hφ : Function.Surjective φ) (n : ℕ) (g : U) :
--       Function.Surjective (pushFibre φ n g) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/RenormalizedFactorizationFiniteLevel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/RenormalizedFactorizationFiniteLevel.lean#L181

-- Thm stub generated from Speculative/AutoResearch/RenormalizedFactorizationFiniteLevel.lean
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

theorem Catalog.Probability.RenormalizedFactorizationFiniteLevel.pushFibre_surjective(φ : U →* V) (hφ : Function.Surjective φ) (n : ℕ) (g : U) :
    Function.Surjective (pushFibre φ n g) := by sorry
