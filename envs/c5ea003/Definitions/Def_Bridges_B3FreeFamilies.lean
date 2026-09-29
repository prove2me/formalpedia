-- Prove2me | Definitions.Def_Bridges_B3FreeFamilies
-- name    : Bridges_B3FreeFamilies
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:39.923443+00:00
-- url     : https://prove2.me/theorems/58c6603a-82f5-487f-a749-2cea18d099fb
-- title:
--   Aether Catalog definitions — Bridges_B3FreeFamilies
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.B3FreeFamilies`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/B3FreeFamilies.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Weak and strong `P`-free families and the layer number `e(P)`

This file formalizes the basic framework surrounding the paper
*On the maximum size of `B_3`-free families*, and proves the exact value of the
"number of free consecutive layers" invariant for the Boolean lattice posets `B_d`.

## Framework

Following the paper, a family `𝒢` of sets is a **weak copy** of a poset `P` if
there is a bijection `ι : P → 𝒢` with `ι p ⊂ ι q` whenever `p < q`, and a
**strong copy** if moreover `ι p ⊂ ι q` holds *only* when `p < q`.  A family is
weak (strong) `P`-free if it contains no weak (strong) copy of `P`.
`La(n, P)` (`La*(n, P)`) is the maximum size of a weak (strong) `P`-free family
in `2^[n]`.

The poset `B_d` is the Boolean lattice on `d` atoms, formalized here as
`Finset (Fin d)` with the inclusion order (`BoolLat d`).

## Main results

* `layers_weakFree` — any `d` consecutive layers of `2^[n]` are weak `B_d`-free;
  hence `e(B_d) ≥ d` and `La(n, B_d) ≥ ∑ᵢ C(n, i)` over `d` consecutive layers
  (`sum_choose_le_La`).
* `exists_strongCopy_layers` — any `d + 1` consecutive layers of `2^[n]`
  (with enough room, `a + d ≤ n`) contain a *strong* copy of `B_d`.
* `weakFree_layers_iff`, `strongFree_layers_iff` — combining the two: `k`
  consecutive layers are weak (strong) `B_d`-free **iff** `k ≤ d`.  This is the
  statement `e(B_d) = e*(B_d) = d`.
* `La_boolLatOne_eq` — **Sperner's theorem in this language**: `La(n, B_1)` is
  exactly `C(n, ⌊n/2⌋)`, i.e. for `d = 1` the layer construction is optimal and
  no `ε`-improvement is possible.  (The content of the paper is that for `d = 3`,
  in contrast, a positive `ε`-improvement does exist.)
* `La_mono_of_strictMono`, `La_boolLat_mono` — `La` is monotone along strictly
  monotone injections of posets, in particular `La(n, B_d) ≤ La(n, B_(d+1))`.
* `mul_choose_le_La`, `three_mul_choose_le_La_boolLat3` — quantitative forms of the
  layer bound, e.g. `3 · C(n, ⌊n/2⌋ - 2) ≤ La(n, B_3)`.
* `La_lt_two_pow`, `La_boolLat_eq_of_card_eq`, `La_boolLat3_fin3` — `La(n, B_d) < 2^n`
  for `d ≤ n`, with the exact values `La(d, B_d) = 2^d - 1` and `La(3, B_3) = 7`.
* `LaStar_boolLat_eq_of_card_eq`, `La_eq_LaStar_of_card_eq` — the same exact value for the
  strong extremal function, so `La(d, B_d) = La*(d, B_d) = 2^d - 1`.

Maximality of the layer construction, the exact value `La(d+1, B_d) = 2^(d+1) - 2`, and the
general upper bound `La(n, B_d) ≤ (2^d - 1)·C(n, ⌊n/2⌋)` are proved in
`Catalog/Bridges/B3FreeFamiliesBounds.lean`.
-/


namespace B3Free

open Finset

/-! ## Weak and strong copies -/

variable {α : Type*}

/-- `ι` realizes a *weak copy* of the poset `P` inside the subsets of `α`:
it is injective and strictly increasing for inclusion. -/
def IsWeakCopy {P : Type*} [Preorder P] (ι : P → Finset α) : Prop :=
  Function.Injective ι ∧ ∀ p q : P, p < q → ι p ⊂ ι q

/-- `ι` realizes a *strong (induced) copy* of the poset `P`: it is injective and
strict inclusion of images happens exactly for strictly comparable elements. -/
def IsStrongCopy {P : Type*} [Preorder P] (ι : P → Finset α) : Prop :=
  Function.Injective ι ∧ ∀ p q : P, ι p ⊂ ι q ↔ p < q

/-- A family `F` is *weak `P`-free* if it contains no weak copy of `P`. -/
def WeakFree (F : Finset (Finset α)) (P : Type*) [Preorder P] : Prop :=
  ¬ ∃ ι : P → Finset α, IsWeakCopy ι ∧ ∀ p, ι p ∈ F

/-- A family `F` is *strong `P`-free* if it contains no strong copy of `P`. -/
def StrongFree (F : Finset (Finset α)) (P : Type*) [Preorder P] : Prop :=
  ¬ ∃ ι : P → Finset α, IsStrongCopy ι ∧ ∀ p, ι p ∈ F





/-! ## Layers of the Boolean lattice -/

variable [DecidableEq α] [Fintype α]

/-- The `k` consecutive layers of `2^α` with sizes in `[a, a + k)`. -/
def layers (α : Type*) [Fintype α] [DecidableEq α] (a k : ℕ) : Finset (Finset α) :=
  {A : Finset α | a ≤ A.card ∧ A.card < a + k}




/-! ## The Boolean lattice poset `B_d` -/

/-- The Boolean lattice poset `B_d`, as the subsets of a `d`-element set. -/
abbrev BoolLat (d : ℕ) : Type := Finset (Fin d)



/-! ## Strong copies inside `d + 1` layers -/

section Construction

variable {d : ℕ} (s : Finset α) (f : Fin d → α)





end Construction




/-! ## The extremal functions `La` and `La*` -/

open scoped Classical in
/-- `La(α, P)`: the maximum size of a weak `P`-free family of subsets of `α`. -/
noncomputable def La (α : Type*) [Fintype α] [DecidableEq α] (P : Type*) [Preorder P] : ℕ :=
  ((Finset.univ : Finset (Finset (Finset α))).filter (fun F => WeakFree F P)).sup Finset.card

open scoped Classical in
/-- `La*(α, P)`: the maximum size of a strong `P`-free family of subsets of `α`. -/
noncomputable def LaStar (α : Type*) [Fintype α] [DecidableEq α] (P : Type*) [Preorder P] : ℕ :=
  ((Finset.univ : Finset (Finset (Finset α))).filter (fun F => StrongFree F P)).sup Finset.card






/-! ## Sperner's theorem: the case `d = 1` -/






/-! ## Monotonicity in the poset, and general bounds -/







/-! ## The case `d = 3`: the setting of the paper -/






/-! ## An exact value: ground set of size exactly `d` -/






end B3Free


