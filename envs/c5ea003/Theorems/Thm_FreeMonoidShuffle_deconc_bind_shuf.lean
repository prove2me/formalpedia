-- Prove2me | Theorems.Thm_FreeMonoidShuffle_deconc_bind_shuf
-- name    : FreeMonoidShuffle.deconc_bind_shuf
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:50:44.986972+00:00
-- url     : https://prove2.me/theorems/fde7735f-031b-4dbf-b305-71fe1f275bd2
-- title:
--   Deconcatenation is an algebra morphism for the shuffle product.
-- statement:
--   **Deconcatenation is an algebra morphism for the shuffle product.**  This is the
--   bialgebra axiom for the commutative, co-noncommutative bialgebra `(K⟨X⟩, ⧢, Δ_conc)`,
--   dual to the concatenation/unshuffle bialgebra.
--
--   ```lean
--   theorem FreeMonoidShuffle.deconc_bind_shuf[DecidableEq X] (u v : List X) :
--       (shuf u v).bind deconc = deconcShufProd u v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DeconcatenationShuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DeconcatenationShuffle.lean#L206

-- Thm stub generated from Novelty/DeconcatenationShuffle.lean
import Mathlib
import Definitions.Def_Novelty_DeconcatenationShuffle
import Definitions.Def_Novelty_FreeMonoidShuffle
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






/-! ## The shuffle product of the tensor square -/




/-! ## The bialgebra axiom -/

theorem FreeMonoidShuffle.deconc_bind_shuf[DecidableEq X] (u v : List X) :
    (shuf u v).bind deconc = deconcShufProd u v := by sorry
