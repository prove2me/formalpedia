-- Prove2me | solution 1 for FreeMonoidShuffle.count_shufPair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:59:07.304094+00:00
-- url     : https://prove2.me/submissions/fff4e78a-77d3-4331-b73c-e7623b03ed5b

-- Sol generated from Novelty/DeconcatenationShuffle.lean
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

lemma sum_map_ite_count [DecidableEq A] (a : A) (s : Multiset A) :
    (s.map (fun z => if a = z then 1 else 0)).sum = Multiset.count a s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons b s ih => simp [ih, Multiset.count_cons, add_comm]







/-! ## The deconcatenation coproduct -/






/-! ## The shuffle product of the tensor square -/




/-! ## The bialgebra axiom -/



open FreeMonoidShuffle in
theorem solution[DecidableEq X] (z1 z2 : List X) (p q : List X × List X) :
    Multiset.count (z1, z2) (shufPair p q)
      = Multiset.count z1 (shuf p.1 q.1) * Multiset.count z2 (shuf p.2 q.2) := by
  rw [shufPair, Multiset.count_bind]
  have hstep : ∀ r : List X,
      Multiset.count (z1, z2) ((shuf p.2 q.2).map (fun s => (r, s)))
        = (if z1 = r then 1 else 0) * Multiset.count z2 (shuf p.2 q.2) := by
    intro r
    induction (shuf p.2 q.2) using Multiset.induction with
    | empty => simp
    | cons b t ih =>
      simp only [Multiset.map_cons, Multiset.count_cons, ih, Multiset.count_cons]
      by_cases h : z1 = r <;> by_cases h2 : z2 = b <;>
        simp [h, h2, Prod.ext_iff, mul_add]
  rw [Multiset.map_congr rfl (fun r _ => hstep r), Multiset.sum_map_mul_right,
    sum_map_ite_count z1]
