-- Prove2me | solution 1 for FreeMonoidShuffle.swap4
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:02:03.406554+00:00
-- url     : https://prove2.me/submissions/0ffc578d-a2b9-44fb-a02a-6cce452f8bff

-- Sol generated from Novelty/DeconcatenationShuffle.lean
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




lemma swap2 (P : Multiset A) (Q : Multiset B) (f : A → B → ℕ) :
    (P.map (fun p => (Q.map (f p)).sum)).sum =
      (Q.map (fun q => (P.map (fun p => f p q)).sum)).sum :=
  Multiset.sum_map_sum_map P Q




/-! ## The deconcatenation coproduct -/






/-! ## The shuffle product of the tensor square -/




/-! ## The bialgebra axiom -/



open FreeMonoidShuffle in
theorem solution(P : Multiset A) (Q : Multiset B) (R : Multiset C) (S : Multiset D)
    (T : A → B → C → D → ℕ) :
    (P.map (fun p => (Q.map (fun q =>
        (R.map (fun r => (S.map (fun s => T p q r s)).sum)).sum)).sum)).sum
      = (R.map (fun r => (S.map (fun s =>
        (P.map (fun p => (Q.map (fun q => T p q r s)).sum)).sum)).sum)).sum := by
  calc (P.map (fun p => (Q.map (fun q =>
          (R.map (fun r => (S.map (fun s => T p q r s)).sum)).sum)).sum)).sum
      = (P.map (fun p => (R.map (fun r =>
          (Q.map (fun q => (S.map (fun s => T p q r s)).sum)).sum)).sum)).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
          swap2 Q R (fun q r => (S.map (fun s => T p q r s)).sum))
    _ = (R.map (fun r => (P.map (fun p =>
          (Q.map (fun q => (S.map (fun s => T p q r s)).sum)).sum)).sum)).sum := swap2 P R _
    _ = (R.map (fun r => (P.map (fun p =>
          (S.map (fun s => (Q.map (fun q => T p q r s)).sum)).sum)).sum)).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl fun r _ => ?_)
        exact congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
          swap2 Q S (fun q s => T p q r s))
    _ = (R.map (fun r => (S.map (fun s =>
          (P.map (fun p => (Q.map (fun q => T p q r s)).sum)).sum)).sum)).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl fun r _ => ?_)
        exact swap2 P S _
