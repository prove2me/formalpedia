-- Prove2me | solution 1 for UnitalMagmaDefect.assocCount_prod
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:24:38.238794+00:00
-- url     : https://prove2.me/submissions/757d2903-8e2e-48e3-8b0b-80b0e6826db3

-- Thm stub generated from Combinatorics/UnitalMagmaDefect.lean
import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect
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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace UMD

theorem assocCount_prod {M N : Type*} [Mul M] [Mul N] [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N] :
    assocCount (M × N) = assocCount M * assocCount N := by
  classical
  have hinj : Function.Injective (fun p : (M × M × M) × (N × N × N) =>
      ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2))) := by
    rintro ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ ⟨⟨c1, c2, c3⟩, ⟨d1, d2, d3⟩⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩⟩ := h
    simp [h1, h2, h3, h4, h5, h6]
  have himg : assocSet (M × N)
      = (assocSet M ×ˢ assocSet N).image (fun p : (M × M × M) × (N × N × N) =>
          ((p.1.1, p.2.1), (p.1.2.1, p.2.2.1), (p.1.2.2, p.2.2.2))) := by
    ext t
    obtain ⟨⟨m1, n1⟩, ⟨m2, n2⟩, ⟨m3, n3⟩⟩ := t
    simp only [assocSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Prod.mk_mul_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨((m1, m2, m3), (n1, n2, n3)), ⟨h1, h2⟩, by simp⟩
    · rintro ⟨⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩, ⟨ha, hb⟩, h⟩
      simp only [Prod.mk.injEq] at h
      obtain ⟨⟨e1, f1⟩, ⟨e2, f2⟩, ⟨e3, f3⟩⟩ := h
      subst e1; subst e2; subst e3; subst f1; subst f2; subst f3
      exact ⟨ha, hb⟩
  rw [assocCount, assocCount, assocCount, himg, Finset.card_image_of_injective _ hinj,
    Finset.card_product]

end UMD

theorem solution : assocCount (M × N) = assocCount M * assocCount N :=
  UMD.assocCount_prod
