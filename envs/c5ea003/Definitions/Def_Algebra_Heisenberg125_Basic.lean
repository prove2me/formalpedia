-- Prove2me | Definitions.Def_Algebra_Heisenberg125_Basic
-- name    : Algebra_Heisenberg125_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:31:37.043875+00:00
-- url     : https://prove2.me/theorems/c0b2198f-7775-4316-8425-2716d8d5c589
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/Basic.lean by skeleton subtraction
import Mathlib
/-
# The Heisenberg group `H_{p^3}` of exponent `p`, and product-one-free sequences

This file sets up the objects needed to study the *small Davenport constant*
`d(G)` (the maximal length of a product-one-free sequence over a finite group
`G`) for the exponent-`p` Heisenberg group

  `H_{p^3} = { (a,b,c) : a,b,c ∈ ZMod p }`,  `(a,b,c)(a',b',c') = (a+a', b+b', c+c'+a b')`,

which is the group of upper unitriangular `3 × 3` matrices over `ZMod p`.

Main contents:

* `Heis p` with its group structure, cardinality `p ^ 3`, commutator formula and
  (for odd `p`) exponent `p`.
* `Heis.crossSum` and the **product formula** `Heis.prod_eq`: the product of a
  list is `(Σ a, Σ b, Σ c + Σ_{i<j} a_i b_j)`.  This is the bridge that turns the
  non-commutative product-one problem into additive combinatorics over
  `(ZMod p)^2`.
* `IsProductOne`, `ProductOneFree`, `smallDavenport` for an arbitrary group, and
  the general pigeonhole bound `d(G) ≤ |G| - 1`.
-/

namespace Heisenberg125

/-! ## The Heisenberg group -/

/-- The Heisenberg group over `ZMod p`: triples `(a,b,c)` with the unitriangular
matrix multiplication. -/
@[ext]
structure Heis (p : ℕ) where
  a : ZMod p
  b : ZMod p
  c : ZMod p
  deriving DecidableEq

namespace Heis

variable {p : ℕ}

instance : Mul (Heis p) := ⟨fun g h => ⟨g.a + h.a, g.b + h.b, g.c + h.c + g.a * h.b⟩⟩
instance : One (Heis p) := ⟨⟨0, 0, 0⟩⟩
instance : Inv (Heis p) := ⟨fun g => ⟨-g.a, -g.b, -g.c + g.a * g.b⟩⟩



@[simp] lemma mul_a (g h : Heis p) : (g * h).a = g.a + h.a := rfl
@[simp] lemma mul_b (g h : Heis p) : (g * h).b = g.b + h.b := rfl
@[simp] lemma mul_c (g h : Heis p) : (g * h).c = g.c + h.c + g.a * h.b := rfl
@[simp] lemma one_a : (1 : Heis p).a = 0 := rfl
@[simp] lemma one_b : (1 : Heis p).b = 0 := rfl
@[simp] lemma one_c : (1 : Heis p).c = 0 := rfl
@[simp] lemma inv_a (g : Heis p) : g⁻¹.a = -g.a := rfl
@[simp] lemma inv_b (g : Heis p) : g⁻¹.b = -g.b := rfl
@[simp] lemma inv_c (g : Heis p) : g⁻¹.c = -g.c + g.a * g.b := rfl

instance : Group (Heis p) :=
  Group.ofLeftAxioms
    (fun g h k => by ext <;> simp <;> ring)
    (fun g => by ext <;> simp)
    (fun g => by ext <;> simp)

/-- The generator `x = (1,0,0)`. -/
def x (p : ℕ) : Heis p := ⟨1, 0, 0⟩
/-- The generator `y = (0,1,0)`. -/
def y (p : ℕ) : Heis p := ⟨0, 1, 0⟩
/-- The central generator `v = [x,y] = (0,0,1)`. -/
def v (p : ℕ) : Heis p := ⟨0, 0, 1⟩





/-! ### Cardinality -/

/-- `Heis p` is in bijection with `(ZMod p)^3`. -/
def equivProd : Heis p ≃ ZMod p × ZMod p × ZMod p where
  toFun g := (g.a, g.b, g.c)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv g := by ext <;> rfl
  right_inv t := rfl

instance [NeZero p] : Fintype (Heis p) := Fintype.ofEquiv _ (equivProd (p := p)).symm


/-! ## Products of lists -/

/-- Sum of the first coordinates. -/
def asum (L : List (Heis p)) : ZMod p := (L.map Heis.a).sum
/-- Sum of the second coordinates. -/
def bsum (L : List (Heis p)) : ZMod p := (L.map Heis.b).sum
/-- Sum of the third coordinates. -/
def csum (L : List (Heis p)) : ZMod p := (L.map Heis.c).sum


/-- The "cross sum" `Σ_{i < j} a_i b_j` of a list. -/
def crossSum : List (Heis p) → ZMod p
  | [] => 0
  | g :: L => g.a * bsum L + crossSum L












end Heis

/-! ## Product-one-free sequences and the small Davenport constant -/

variable {G : Type*} [Group G]

/-- A sequence (list) over a group *has product one* if some ordering of it
multiplies to `1`. -/
def IsProductOne (L : List G) : Prop := ∃ M : List G, M.Perm L ∧ M.prod = 1

/-- A sequence is *product-one-free* if no nonempty subsequence has product one
in any ordering. -/
def ProductOneFree (L : List G) : Prop :=
  ∀ T : List G, T.Sublist L → T ≠ [] → ¬ IsProductOne T


/-- The set of lengths of product-one-free sequences. -/
def productOneFreeLengths (G : Type*) [Group G] : Set ℕ :=
  {n | ∃ L : List G, L.length = n ∧ ProductOneFree L}

/-- The **small Davenport constant** `d(G)`: the maximal length of a
product-one-free sequence over `G`. -/
noncomputable def smallDavenport (G : Type*) [Group G] : ℕ :=
  sSup (productOneFreeLengths G)








end Heisenberg125


