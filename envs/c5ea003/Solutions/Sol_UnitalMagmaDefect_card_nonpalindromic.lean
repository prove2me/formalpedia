-- Prove2me | solution 1 for UnitalMagmaDefect.card_nonpalindromic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:24:39.167343+00:00
-- url     : https://prove2.me/submissions/71b71758-4e79-4f3e-a18d-39f981c647e3

-- Thm stub generated from Combinatorics/UnitalMagmaDefect.lean
import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace UMD

theorem card_nonpalindromic {M : Type*} [DecidableEq M] (S : Finset M) :
    ((S ×ˢ (S ×ˢ S)).filter fun t => t.1 ≠ t.2.2).card = S.card ^ 3 - S.card ^ 2 := by
  classical
  have htot : (S ×ˢ (S ×ˢ S)).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product]; ring
  have hinj : Function.Injective (fun p : M × M => (p.1, p.2, p.1)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    simp [h.1, h.2.1]
  have himg : ((S ×ˢ (S ×ˢ S)).filter fun t : M × M × M => ¬ (t.1 ≠ t.2.2))
      = (S ×ˢ S).image (fun p : M × M => (p.1, p.2, p.1)) := by
    ext t
    obtain ⟨a, b, c⟩ := t
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, not_not, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨ha, hb, hc⟩, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl, rfl, rfl⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, h1, h2, h3⟩
      subst h1; subst h2; subst h3
      exact ⟨⟨hx, hy, hx⟩, rfl⟩
  have hpal : ((S ×ˢ (S ×ˢ S)).filter fun t : M × M × M => ¬ (t.1 ≠ t.2.2)).card = S.card ^ 2 := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_product]; ring
  have hsum := Finset.card_filter_add_card_filter_not
    (s := S ×ˢ (S ×ˢ S)) (p := fun t : M × M × M => t.1 ≠ t.2.2)
  omega

end UMD

/-
# The associativity defect of a finite unital magma

This file is the combinatorial counterpart of `Catalog/Combinatorics/CodiscreteMagmaBicategory.lean`.
There we showed that *every* pointed magma `M` produces a coherent bicategory `MagmaBicat M`
whose weak associator repairs the associativity defect of `M`.  Here we measure that defect.

For a finite pointed magma we set
`defect M = #{(a,b,c) : (a*b)*c ≠ a*(b*c)}`.

Main results:
* `UnitalMagmaDefect.defect_eq_zero_iff` : `defect M = 0` iff `M` is associative;
* `UnitalMagmaDefect.assocCount_prod` : the number of *associative* triples is multiplicative
  under products of magmas, i.e. the associativity density is multiplicative;
* `UnitalMagmaDefect.defect_congr` and `UnitalMagmaDefect.defect_op` : the defect is invariant
  under magma isomorphism and under passing to the opposite magma;
* `UnitalMagmaDefect.defect_even_of_comm` : the defect of a finite **commutative** magma is
  always even (reversal involution, palindromic triples are never defective), whence
  `defect_ne_one_of_comm`;
* `UnitalMagmaDefect.defect_le_of_comm_unital` and
  `UnitalMagmaDefect.exists_comm_unital_magma_maximal_defect` : the sharp commutative bound
  `(n-1)^3 - (n-1)^2`, attained by the *negation magma* `NegMagma (ZMod m)` for odd `m`;
* `UnitalMagmaDefect.card_nonidentity_associators` and `strict_iff_defect_zero` : the bridge to
  the bicategory, `defect M` counts the non-identity associator instances of `MagmaBicat M`;
* `UnitalMagmaDefect.defect_le_of_unital` : if `1` is a two-sided unit then no defect triple can
  involve `1`, whence `defect M ≤ (card M - 1) ^ 3`;
* `UnitalMagmaDefect.ShiftMagma.defect_eq` : the *shift magma* `ShiftMagma σ = Option S`
  attached to a fixed-point-free self-map `σ : S → S` is a unital magma **every** one of whose
  non-unit triples is defective, so it attains the bound;
* `UnitalMagmaDefect.exists_unital_magma_maximal_defect` : for every `n ≥ 3` there is a unital
  magma of cardinality `n` with `defect = (n-1)^3`, i.e. the bound above is sharp;
* `UnitalMagmaDefect.AdjoinOne.defect_eq` : freely adjoining a unit to a magma changes no
  associativity defect, so every defect profile occurs for a *unital* magma;
* `UnitalMagmaDefect.shiftMagma_not_strict` / `shiftMagma_coherent` : the corresponding
  codiscrete bicategory is genuinely weak (not strict), yet all of its 2-cells are invertible
  and any two parallel 2-cells agree.
-/

universe u

open Finset CategoryTheory

open UnitalMagmaDefect


variable (M : Type u) [Mul M] [Fintype M] [DecidableEq M]



variable {M}










variable {M : Type u} {N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]







variable {M : Type u} {N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]





variable {M : Type u} [Mul M] [Fintype M] [DecidableEq M] (hcomm : ∀ a b : M, a * b = b * a)

include hcomm







variable {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
  (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a)

include hl hr





variable {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]

omit [Mul M] [One M] [Fintype M] in

theorem solution (S : Finset M) :
    ((S ×ˢ (S ×ˢ S)).filter fun t => t.1 ≠ t.2.2).card = S.card ^ 3 - S.card ^ 2 :=
  UMD.card_nonpalindromic S
