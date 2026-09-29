-- Prove2me | Definitions.Def_Combinatorics_UnitalMagmaDefect
-- name    : Combinatorics_UnitalMagmaDefect
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:57:23.601603+00:00
-- url     : https://prove2.me/theorems/6094997e-41d6-4379-b026-ba7188982b16
-- title:
--   Aether Catalog definitions — Combinatorics_UnitalMagmaDefect
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.UnitalMagmaDefect`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/UnitalMagmaDefect.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
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

namespace UnitalMagmaDefect

section Defect

variable (M : Type u) [Mul M] [Fintype M] [DecidableEq M]

/-- The set of triples at which associativity fails. -/
def defectSet : Finset (M × M × M) :=
  univ.filter fun t => (t.1 * t.2.1) * t.2.2 ≠ t.1 * (t.2.1 * t.2.2)

/-- The associativity defect of a finite magma: the number of non-associative triples. -/
def defect : ℕ := (defectSet M).card

variable {M}




/-- The set of triples at which associativity holds. -/
def assocSet (M : Type u) [Mul M] [Fintype M] [DecidableEq M] : Finset (M × M × M) :=
  univ.filter fun t => (t.1 * t.2.1) * t.2.2 = t.1 * (t.2.1 * t.2.2)

/-- The number of associative triples of a finite magma. -/
def assocCount (M : Type u) [Mul M] [Fintype M] [DecidableEq M] : ℕ := (assocSet M).card



end Defect

section Product

variable {M : Type u} {N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]



end Product

section Invariance

/-- The opposite of a finite type is finite. -/
instance fintypeMulOpposite (α : Type u) [Fintype α] : Fintype αᵐᵒᵖ :=
  ⟨(Finset.univ : Finset α).map ⟨MulOpposite.op, MulOpposite.op_injective⟩, by
    intro x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨x.unop, rfl⟩⟩

/-- Equality in the opposite type is decidable. -/
instance decidableEqMulOpposite (α : Type u) [DecidableEq α] : DecidableEq αᵐᵒᵖ :=
  fun x y => decidable_of_iff (x.unop = y.unop)
    ⟨fun h => MulOpposite.unop_injective h, fun h => by rw [h]⟩

variable {M : Type u} {N : Type u} [Mul M] [Mul N] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]



end Invariance

section Commutative

variable {M : Type u} [Mul M] [Fintype M] [DecidableEq M] (hcomm : ∀ a b : M, a * b = b * a)

include hcomm





end Commutative

section Unital

variable {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]
  (hl : ∀ a : M, (1 : M) * a = a) (hr : ∀ a : M, a * (1 : M) = a)

include hl hr



end Unital

section CommutativeUnital

variable {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]



end CommutativeUnital

/-! ### The shift magma: a unital magma of maximal defect -/

/-- The **shift magma** attached to a self-map `σ : S → S`: the underlying type is `Option S`,
`none` is a two-sided unit, and the product of two non-units `some a`, `some b` is `some (σ b)`.
-/
@[nolint unusedArguments]
def ShiftMagma {S : Type u} (_σ : S → S) : Type u := Option S

namespace ShiftMagma

variable {S : Type u} (σ : S → S)

instance : One (ShiftMagma σ) := ⟨(none : Option S)⟩

instance : Mul (ShiftMagma σ) :=
  ⟨fun x y =>
    match (x : Option S), (y : Option S) with
    | none, y => y
    | x, none => x
    | some _, some b => (some (σ b) : Option S)⟩

instance [DecidableEq S] : DecidableEq (ShiftMagma σ) := inferInstanceAs (DecidableEq (Option S))

instance [Fintype S] : Fintype (ShiftMagma σ) := inferInstanceAs (Fintype (Option S))

/-- The element of `ShiftMagma σ` named by `a : S`. -/
def of (a : S) : ShiftMagma σ := (some a : Option S)

variable {σ}








variable [Fintype S] [DecidableEq S]




end ShiftMagma

/-! ### Sharpness of the bound for every cardinality -/

/-- The cyclic shift on `Fin m`, for `m ≥ 2`: a fixed-point-free self-map. -/
def cyclicShift (m : ℕ) (c : Fin m) : Fin m :=
  if h : c.val + 1 < m then ⟨c.val + 1, h⟩ else ⟨0, lt_of_le_of_lt (Nat.zero_le _) c.isLt⟩



/-! ### The negation magma: a commutative unital magma of maximal defect -/

/-- The **negation magma** of an additive abelian group `G`: the underlying type is `Option G`,
`none` is a two-sided unit, and `some a * some b = some (-(a + b))`. -/
def NegMagma (G : Type u) [AddCommGroup G] : Type u := Option G

namespace NegMagma

variable {G : Type u} [AddCommGroup G]

instance : One (NegMagma G) := ⟨(none : Option G)⟩

instance : Mul (NegMagma G) :=
  ⟨fun x y =>
    match (x : Option G), (y : Option G) with
    | none, y => y
    | x, none => x
    | some a, some b => (some (-(a + b)) : Option G)⟩

instance [DecidableEq G] : DecidableEq (NegMagma G) := inferInstanceAs (DecidableEq (Option G))

instance [Fintype G] : Fintype (NegMagma G) := inferInstanceAs (Fintype (Option G))

/-- The element of `NegMagma G` named by `a : G`. -/
def of (a : G) : NegMagma G := (some a : Option G)







variable [Fintype G] [DecidableEq G]



end NegMagma


/-! ### Adjoining a unit does not change the defect -/

/-- Freely adjoining a unit to a magma `α`. -/
def AdjoinOne (α : Type u) : Type u := Option α

namespace AdjoinOne

variable {α : Type u} [Mul α]

instance : One (AdjoinOne α) := ⟨(none : Option α)⟩

instance : Mul (AdjoinOne α) :=
  ⟨fun x y =>
    match (x : Option α), (y : Option α) with
    | none, y => y
    | x, none => x
    | some a, some b => (some (a * b) : Option α)⟩

instance [DecidableEq α] : DecidableEq (AdjoinOne α) := inferInstanceAs (DecidableEq (Option α))

instance [Fintype α] : Fintype (AdjoinOne α) := inferInstanceAs (Fintype (Option α))

/-- The image of `a : α` in `AdjoinOne α`. -/
def of (a : α) : AdjoinOne α := (some a : Option α)







variable [Fintype α] [DecidableEq α]



end AdjoinOne

/-! ### A worked example: the smallest maximal-defect unital magma -/

/-! ### Consequences for the codiscrete bicategory -/

open CodiscreteMagma



variable {M : Type u} [Mul M] [One M] [Fintype M] [DecidableEq M]

/-- 1-cells of `MagmaBicat M` have decidable equality when `M` does. -/
instance decidableEqOneCell : DecidableEq (star M ⟶ star M) :=
  inferInstanceAs (DecidableEq (Codiscrete M))



end UnitalMagmaDefect


