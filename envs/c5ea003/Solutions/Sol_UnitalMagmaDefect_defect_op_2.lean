-- Prove2me | solution 2 for UnitalMagmaDefect.defect_op
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T02:24:37.471339+00:00
-- url     : https://prove2.me/submissions/83adacf4-da85-4ea2-9b30-c408ffd3d01c

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







variable {M : Type u} {N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace UMD

theorem defect_op {M : Type*} [Mul M] [Fintype M] [DecidableEq M] :
    defect (Mᵐᵒᵖ) = defect M := by
  classical
  have key : ∀ A B C : Mᵐᵒᵖ, ((A * B) * C = A * (B * C))
      ↔ ((C.unop * B.unop) * A.unop = C.unop * (B.unop * A.unop)) := by
    intro A B C
    constructor
    · intro h
      simpa [MulOpposite.unop_mul] using (congrArg MulOpposite.unop h).symm
    · intro h
      apply MulOpposite.unop_injective
      simpa [MulOpposite.unop_mul] using h.symm
  have hinj : Function.Injective
      (fun t : Mᵐᵒᵖ × Mᵐᵒᵖ × Mᵐᵒᵖ => (t.2.2.unop, t.2.1.unop, t.1.unop)) := by
    rintro ⟨a1, b1, c1⟩ ⟨a2, b2, c2⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    simp [MulOpposite.unop_injective h1, MulOpposite.unop_injective h2,
      MulOpposite.unop_injective h3]
  have himg : defectSet M
      = (defectSet Mᵐᵒᵖ).image (fun t : Mᵐᵒᵖ × Mᵐᵒᵖ × Mᵐᵒᵖ => (t.2.2.unop, t.2.1.unop, t.1.unop)) := by
    ext t
    simp only [defectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨(MulOpposite.op t.2.2, MulOpposite.op t.2.1, MulOpposite.op t.1), ?_, by simp⟩
      intro hc
      exact h (by simpa using (key _ _ _).1 hc)
    · rintro ⟨s, hs, rfl⟩
      intro hc
      exact hs ((key _ _ _).2 hc)
  rw [defect, defect, himg, Finset.card_image_of_injective _ hinj]

end UMD

theorem solution : defect (Mᵐᵒᵖ) = defect M :=
  UMD.defect_op
