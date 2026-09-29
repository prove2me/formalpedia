-- Prove2me | Theorems.Thm_UnitalMagmaDefect_defect_even_of_comm
-- name    : UnitalMagmaDefect.defect_even_of_comm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:36:55.234833+00:00
-- url     : https://prove2.me/theorems/49910956-a7f3-4175-ae75-6214080ce989
-- title:
--   Parity theorem.
-- statement:
--   **Parity theorem.**  The associativity defect of a finite *commutative* magma is always even:
--   the reversal involution `(a,b,c) ↦ (c,b,a)` acts on the defect set without fixed points, since
--   palindromic triples are automatically associative.
--
--   ```lean
--   theorem UnitalMagmaDefect.defect_even_of_comm: Even (defect M) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/UnitalMagmaDefect.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/UnitalMagmaDefect.lean#L217

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





variable {M : Type u} [Mul M] [Fintype M] [DecidableEq M] (hcomm : ∀ a b : M, a * b = b * a)

include hcomm

theorem UnitalMagmaDefect.defect_even_of_comm: Even (defect M) := by sorry
