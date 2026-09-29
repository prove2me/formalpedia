-- Prove2me | solution 2 for FreeMonoidShuffle.count_deconc
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:11:05.260099+00:00
-- url     : https://prove2.me/submissions/550fd6ef-1d0a-4a88-ae53-c6081ca09c4a

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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace FMS

theorem deconc_nil : deconc ([] : List X) = {([], [])} := rfl

theorem deconc_cons (a : X) (w : List X) :
    deconc (a :: w)
      = (([], a :: w) : List X × List X) ::ₘ ((deconc w).map (fun p => (a :: p.1, p.2))) := rfl

/-! ### Grading -/

theorem count_deconc [DecidableEq X] (z1 z2 z : List X) :
    Multiset.count (z1, z2) (deconc z) = if z1 ++ z2 = z then 1 else 0 := by
  induction z generalizing z1 with
  | nil =>
    rw [deconc_nil]
    by_cases h : z1 ++ z2 = ([] : List X)
    · obtain ⟨rfl, rfl⟩ : z1 = [] ∧ z2 = [] := by simpa using h
      simp
    · rw [if_neg h, Multiset.count_eq_zero]
      simp only [Multiset.mem_singleton, Prod.mk.injEq, not_and]
      rintro rfl rfl
      exact h (by simp)
  | cons a w ih =>
    have hinj : Function.Injective (fun p : List X × List X => (a :: p.1, p.2)) := by
      rintro ⟨x1, x2⟩ ⟨y1, y2⟩ hxy
      simpa using hxy
    rw [deconc_cons, Multiset.count_cons]
    match z1 with
    | [] =>
      have hz : Multiset.count (([], z2) : List X × List X)
          ((deconc w).map (fun p => (a :: p.1, p.2))) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hm
        obtain ⟨p, -, hp⟩ := Multiset.mem_map.1 hm
        simpa using congrArg Prod.fst hp
      rw [hz, zero_add, List.nil_append]
      by_cases h : z2 = a :: w
      · subst h; simp
      · rw [if_neg h, if_neg]
        simp only [Prod.mk.injEq, not_and]
        exact fun _ => h
    | c :: z1 =>
      have hne : ((c :: z1, z2) : List X × List X) ≠ ([], a :: w) := by simp
      rw [if_neg hne, add_zero]
      by_cases hca : c = a
      · subst hca
        rw [show ((c :: z1, z2) : List X × List X)
            = (fun p : List X × List X => (c :: p.1, p.2)) (z1, z2) from rfl,
          Multiset.count_map_eq_count' _ _ hinj, ih]
        by_cases h : z1 ++ z2 = w
        · rw [if_pos h, if_pos (by rw [List.cons_append, h])]
        · rw [if_neg h, if_neg]
          intro hc
          simp only [List.cons_append, List.cons.injEq] at hc
          exact h hc.2
      · have hz : Multiset.count ((c :: z1, z2) : List X × List X)
            ((deconc w).map (fun p => (a :: p.1, p.2))) = 0 := by
          rw [Multiset.count_eq_zero]
          intro hm
          obtain ⟨p, -, hp⟩ := Multiset.mem_map.1 hm
          have hfst := congrArg Prod.fst hp
          simp only [List.cons.injEq] at hfst
          exact hca hfst.1.symm
        rw [hz, if_neg]
        intro hc
        simp only [List.cons_append, List.cons.injEq] at hc
        exact hca hc.1

/-! ### Shuffle/unshuffle duality -/

end FMS

theorem solution [DecidableEq X] (z1 z2 z : List X) :
    Multiset.count (z1, z2) (deconc z) = if z1 ++ z2 = z then 1 else 0 :=
  FMS.count_deconc z1 z2 z
