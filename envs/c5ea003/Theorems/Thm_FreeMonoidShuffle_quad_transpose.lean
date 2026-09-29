-- Prove2me | Theorems.Thm_FreeMonoidShuffle_quad_transpose
-- name    : FreeMonoidShuffle.quad_transpose
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:50:12.267617+00:00
-- url     : https://prove2.me/theorems/841cbd4c-d81d-4789-9f0d-a7b9b80678f6
-- title:
--   The four-fold transposition identity for counting matched pairs.
-- statement:
--   The four-fold transposition identity for counting matched pairs.
--
--   ```lean
--   theorem FreeMonoidShuffle.quad_transpose[DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
--       (P : Multiset (A × B)) (Q : Multiset (C × D))
--       (R : Multiset (A × C)) (S : Multiset (B × D)) :
--       (P.map (fun p => (Q.map (fun q =>
--           Multiset.count (p.1, q.1) R * Multiset.count (p.2, q.2) S)).sum)).sum
--         = (R.map (fun r => (S.map (fun s =>
--           Multiset.count (r.1, s.1) P * Multiset.count (r.2, s.2) Q)).sum)).sum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/DeconcatenationShuffle.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/DeconcatenationShuffle.lean#L82

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

theorem FreeMonoidShuffle.quad_transpose[DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (P : Multiset (A × B)) (Q : Multiset (C × D))
    (R : Multiset (A × C)) (S : Multiset (B × D)) :
    (P.map (fun p => (Q.map (fun q =>
        Multiset.count (p.1, q.1) R * Multiset.count (p.2, q.2) S)).sum)).sum
      = (R.map (fun r => (S.map (fun s =>
        Multiset.count (r.1, s.1) P * Multiset.count (r.2, s.2) Q)).sum)).sum := by sorry
