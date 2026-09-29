-- Prove2me | Theorems.Thm_FreeMonoidShuffle_count_deconc
-- name    : FreeMonoidShuffle.count_deconc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:49:50.454959+00:00
-- url     : https://prove2.me/theorems/442b5c7e-a9f4-4836-a130-cd31d6d7cb97
-- title:
--   The coefficients of the deconcatenation coproduct: `(z₁, z₂)` occurs in `Δ_conc(z)`
-- statement:
--   The coefficients of the deconcatenation coproduct: `(z₁, z₂)` occurs in `Δ_conc(z)`
--   exactly when `z = z₁ z₂`, and then with multiplicity one.
--
--   ```lean
--   theorem FreeMonoidShuffle.count_deconc[DecidableEq X] (z1 z2 z : List X) :
--       Multiset.count (z1, z2) (deconc z) = if z1 ++ z2 = z then 1 else 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DeconcatenationShuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DeconcatenationShuffle.lean#L151

-- Thm stub generated from Novelty/DeconcatenationShuffle.lean
import Mathlib
import Definitions.Def_Novelty_DeconcatenationShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
/-
# The deconcatenation coproduct and the shuffle bialgebra

This file completes the picture of `Novelty.FreeMonoidUnshuffle` by treating the *other*
of the two mutually dual bialgebra structures on `K⟨X⟩`:

* `(K⟨X⟩, concatenation, Δ_⧢)` — the graded noncommutative co-commutative bialgebra,
  handled in `Novelty.FreeMonoidUnshuffle` (`unsh_append`, `unsh_coassoc`);
* `(K⟨X⟩, ⧢, Δ_conc)` — the commutative, co-noncommutative bialgebra of this file,
  where `Δ_conc(w) = Σ_{w = z₁z₂} z₁ ⊗ z₂` is the deconcatenation coproduct.

The main theorem `deconc_bind_shuf` is the bialgebra axiom for the second structure:
deconcatenation is an algebra morphism for the shuffle product,

`Δ_conc(u ⧢ v) = Δ_conc(u) ⧢₂ Δ_conc(v)`,

where `⧢₂` is the shuffle product of the tensor square.  The proof is *by duality*: both
sides are computed coefficientwise, the coefficients are transported to the unshuffle
side through `count_shuf_eq_count_unsh`, and there they become the multiplicativity of
the unshuffle coproduct `unsh_append`, up to a purely combinatorial four-fold
transposition of counting sums (`quad_transpose`).
-/

open FreeMonoidShuffle

variable {X : Type*}

/-! ## Elementary counting lemmas -/

variable {A B C D : Type*}








/-! ## The deconcatenation coproduct -/

theorem FreeMonoidShuffle.count_deconc[DecidableEq X] (z1 z2 z : List X) :
    Multiset.count (z1, z2) (deconc z) = if z1 ++ z2 = z then 1 else 0 := by sorry
