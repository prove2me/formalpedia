-- Prove2me | solution 1 for FreeMonoidShuffle.deconc_bind_shuf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:06:26.090466+00:00
-- url     : https://prove2.me/submissions/f64cf1f1-2fb0-4080-803f-bd6f3f389792

-- Sol generated from Novelty/DeconcatenationShuffle.lean
import Mathlib
import Definitions.Def_Novelty_DeconcatenationShuffle
import Definitions.Def_Novelty_FreeMonoidShuffle
import Definitions.Def_Novelty_FreeMonoidUnshuffle
import Theorems.Thm_FreeMonoidShuffle_count_deconc
import Theorems.Thm_FreeMonoidShuffle_count_shufPair
import Theorems.Thm_FreeMonoidShuffle_count_shuf_eq_count_unsh
import Theorems.Thm_FreeMonoidShuffle_quad_transpose
import Theorems.Thm_FreeMonoidShuffle_unsh_append
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

lemma count_map_eq_sum_ite [DecidableEq A] [DecidableEq B] (b : B) (f : A → B)
    (s : Multiset A) :
    Multiset.count b (s.map f) = (s.map (fun a => if b = f a then 1 else 0)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [ih, Multiset.count_cons, add_comm]






/-! ## The deconcatenation coproduct -/






/-! ## The shuffle product of the tensor square -/




/-! ## The bialgebra axiom -/



open FreeMonoidShuffle in
theorem solution[DecidableEq X] (u v : List X) :
    (shuf u v).bind deconc = deconcShufProd u v := by
  ext z
  obtain ⟨z1, z2⟩ := z
  -- the left hand side counts the shuffles of `u` and `v` equal to `z₁z₂`
  have hleft : Multiset.count (z1, z2) ((shuf u v).bind deconc)
      = Multiset.count (u, v) (pairMul (unsh z1) (unsh z2)) := by
    rw [Multiset.count_bind,
      Multiset.map_congr rfl (fun z _ => count_deconc z1 z2 z)]
    have : (Multiset.map (fun z => if z1 ++ z2 = z then 1 else 0) (shuf u v)).sum
        = Multiset.count (z1 ++ z2) (shuf u v) := sum_map_ite_count _ _
    rw [this, count_shuf_eq_count_unsh, unsh_append]
  -- the right hand side is the same count, transposed
  have hright : Multiset.count (z1, z2) (deconcShufProd u v)
      = ((unsh z1).map (fun al => ((unsh z2).map (fun be =>
          Multiset.count (al.1, be.1) (deconc u) *
            Multiset.count (al.2, be.2) (deconc v))).sum)).sum := by
    rw [deconcShufProd, Multiset.count_bind]
    have hin : ∀ p : List X × List X,
        Multiset.count (z1, z2) ((deconc v).bind (fun q => shufPair p q))
          = ((deconc v).map (fun q =>
              Multiset.count (p.1, q.1) (unsh z1) * Multiset.count (p.2, q.2) (unsh z2))).sum := by
      intro p
      rw [Multiset.count_bind]
      refine congrArg Multiset.sum (Multiset.map_congr rfl fun q _ => ?_)
      rw [count_shufPair, count_shuf_eq_count_unsh, count_shuf_eq_count_unsh]
    rw [Multiset.map_congr rfl (fun p _ => hin p)]
    exact quad_transpose (deconc u) (deconc v) (unsh z1) (unsh z2)
  rw [hleft, hright, pairMul, Multiset.count_bind]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun al _ => ?_)
  rw [count_map_eq_sum_ite]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun be _ => ?_)
  rw [count_deconc, count_deconc]
  by_cases h1 : al.1 ++ be.1 = u <;> by_cases h2 : al.2 ++ be.2 = v <;>
    simp [h1, h2, Prod.ext_iff, eq_comm] <;> tauto
