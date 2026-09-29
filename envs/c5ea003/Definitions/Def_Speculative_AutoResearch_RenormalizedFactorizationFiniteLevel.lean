-- Prove2me | Definitions.Def_Speculative_AutoResearch_RenormalizedFactorizationFiniteLevel
-- name    : Speculative_AutoResearch_RenormalizedFactorizationFiniteLevel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:30:01.394268+00:00
-- url     : https://prove2.me/theorems/113c5a0c-782e-4834-a7d6-a38c520d483d
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_RenormalizedFactorizationFiniteLevel
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.RenormalizedFactorizationFiniteLevel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/RenormalizedFactorizationFiniteLevel.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Probability.RenormalizedFactorizationFiniteLevel

open Finset

/-! ## The truncated fibre -/

variable {U : Type*} [CommGroup U]

/-- **The fibre of the `m = n + 1`-fold product map is `n` free slots.**  An `m`-tuple with
prescribed product is the same thing as an arbitrary choice of its last `n` entries: the zeroth
entry is forced to be `g * (∏ rest)⁻¹`. -/
def fibreEquivFun (n : ℕ) (g : U) :
    {f : Fin (n + 1) → U // ∏ i, f i = g} ≃ (Fin n → U) where
  toFun f := fun j => f.1 j.succ
  invFun w := ⟨Fin.cons (g * (∏ j, w j)⁻¹) w, by rw [Fin.prod_univ_succ]; simp⟩
  left_inv := by
    intro f
    apply Subtype.ext
    have h' : f.1 0 * ∏ j : Fin n, f.1 j.succ = g := by
      rw [← Fin.prod_univ_succ]; exact f.2
    funext i
    dsimp only
    refine Fin.cases ?_ ?_ i
    · rw [Fin.cons_zero]; exact (eq_mul_inv_of_mul_eq h').symm
    · intro j; rw [Fin.cons_succ]
  right_inv := by
    intro w; funext j; simp



/-! ## Level `D` over `ℤ_p`: the predicted count `((q₀ - 1) q₀ ^ (D-1)) ^ (m-1)` -/

variable (p D n : ℕ) [Fact p.Prime]

/-- The unit group of `ZMod (p ^ D)` is nontrivial as a finite type. -/
instance : NeZero (p ^ D) := ⟨pow_ne_zero _ (Nat.Prime.ne_zero Fact.out)⟩



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

section Transition

variable {V : Type*} [CommGroup V]

/-- Push a factorization forward along a group homomorphism. -/
def pushFibre (φ : U →* V) (n : ℕ) (g : U) :
    {f : Fin (n + 1) → U // ∏ i, f i = g} → {f : Fin (n + 1) → V // ∏ i, f i = φ g} :=
  fun f => ⟨fun i => φ (f.1 i), by rw [← map_prod, f.2]⟩


end Transition


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

end Catalog.Probability.RenormalizedFactorizationFiniteLevel


