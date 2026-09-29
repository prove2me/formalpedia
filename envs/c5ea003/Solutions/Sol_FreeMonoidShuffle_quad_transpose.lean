-- Prove2me | solution 1 for FreeMonoidShuffle.quad_transpose
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:04:51.482985+00:00
-- url     : https://prove2.me/submissions/70b618bc-e4c6-42bf-b6d6-bfb04a462984

-- Sol generated from Novelty/DeconcatenationShuffle.lean
import Mathlib
import Definitions.Def_Novelty_DeconcatenationShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Theorems.Thm_FreeMonoidShuffle_swap4
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

lemma sum_map_ite_count [DecidableEq A] (a : A) (s : Multiset A) :
    (s.map (fun z => if a = z then 1 else 0)).sum = Multiset.count a s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih => simp [ih, Multiset.count_cons, add_comm]


lemma prodsum (U : Multiset A) (V : Multiset B) (f : A → ℕ) (g : B → ℕ) :
    (U.map f).sum * (V.map g).sum = (U.map (fun x => (V.map (fun y => f x * g y)).sum)).sum := by
  rw [← Multiset.sum_map_mul_right]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun x _ =>
    (Multiset.sum_map_mul_left).symm)





/-! ## The deconcatenation coproduct -/






/-! ## The shuffle product of the tensor square -/




/-! ## The bialgebra axiom -/



open FreeMonoidShuffle in
theorem solution[DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (P : Multiset (A × B)) (Q : Multiset (C × D))
    (R : Multiset (A × C)) (S : Multiset (B × D)) :
    (P.map (fun p => (Q.map (fun q =>
        Multiset.count (p.1, q.1) R * Multiset.count (p.2, q.2) S)).sum)).sum
      = (R.map (fun r => (S.map (fun s =>
        Multiset.count (r.1, s.1) P * Multiset.count (r.2, s.2) Q)).sum)).sum := by
  have hL : ∀ (p : A × B) (q : C × D),
      Multiset.count (p.1, q.1) R * Multiset.count (p.2, q.2) S
        = (R.map (fun r => (S.map (fun s =>
            (if (p.1, q.1) = r then 1 else 0) * (if (p.2, q.2) = s then 1 else 0))).sum)).sum := by
    intro p q
    rw [← sum_map_ite_count (p.1, q.1) R, ← sum_map_ite_count (p.2, q.2) S, prodsum]
  have hR : ∀ (r : A × C) (s : B × D),
      Multiset.count (r.1, s.1) P * Multiset.count (r.2, s.2) Q
        = (P.map (fun p => (Q.map (fun q =>
            (if (r.1, s.1) = p then 1 else 0) * (if (r.2, s.2) = q then 1 else 0))).sum)).sum := by
    intro r s
    rw [← sum_map_ite_count (r.1, s.1) P, ← sum_map_ite_count (r.2, s.2) Q, prodsum]
  have hT : ∀ (p : A × B) (q : C × D) (r : A × C) (s : B × D),
      (if (p.1, q.1) = r then 1 else 0) * (if (p.2, q.2) = s then 1 else 0)
        = (if (r.1, s.1) = p then 1 else 0) * ((if (r.2, s.2) = q then 1 else 0) : ℕ) := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ ⟨r1, r2⟩ ⟨s1, s2⟩
    simp only [Prod.mk.injEq]
    by_cases h1 : p1 = r1 <;> by_cases h2 : q1 = r2 <;> by_cases h3 : p2 = s1 <;>
      by_cases h4 : q2 = s2 <;> simp [h1, h2, h3, h4, eq_comm]
  calc (P.map (fun p => (Q.map (fun q =>
          Multiset.count (p.1, q.1) R * Multiset.count (p.2, q.2) S)).sum)).sum
      = (P.map (fun p => (Q.map (fun q => (R.map (fun r => (S.map (fun s =>
          (if (p.1, q.1) = r then 1 else 0) *
            (if (p.2, q.2) = s then 1 else 0))).sum)).sum)).sum)).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
          congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => hL p q))
    _ = (R.map (fun r => (S.map (fun s => (P.map (fun p => (Q.map (fun q =>
          (if (p.1, q.1) = r then 1 else 0) *
            (if (p.2, q.2) = s then 1 else 0))).sum)).sum)).sum)).sum := swap4 _ _ _ _ _
    _ = (R.map (fun r => (S.map (fun s => (P.map (fun p => (Q.map (fun q =>
          (if (r.1, s.1) = p then 1 else 0) *
            (if (r.2, s.2) = q then 1 else 0))).sum)).sum)).sum)).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl fun r _ =>
          congrArg Multiset.sum (Multiset.map_congr rfl fun s _ =>
            congrArg Multiset.sum (Multiset.map_congr rfl fun p _ =>
              congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => hT p q r s))))
    _ = (R.map (fun r => (S.map (fun s =>
          Multiset.count (r.1, s.1) P * Multiset.count (r.2, s.2) Q)).sum)).sum :=
        congrArg Multiset.sum (Multiset.map_congr rfl fun r _ =>
          congrArg Multiset.sum (Multiset.map_congr rfl fun s _ => (hR r s).symm))
