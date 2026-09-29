-- Prove2me | Definitions.Def_Applications_PosetTheory_MatroidMinorBasic
-- name    : Applications_PosetTheory_MatroidMinorBasic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:33.979975+00:00
-- url     : https://prove2.me/theorems/e154921a-26e0-44ea-8e75-37e39bbe7a39
-- title:
--   Aether Catalog definitions — Applications_PosetTheory_MatroidMinorBasic
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PosetTheory.MatroidMinorBasic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PosetTheory/MatroidMinorBasic.lean by skeleton subtraction
import Mathlib

/-!
# Minor-closed classes, excluded minors and representability

This file sets up the basic vocabulary of matroid minor theory that is used in
`Applications/PosetTheory/Structural.lean`:

* `MinorClosed P` — the class `P` is closed under taking minors;
* `IsForbiddenMinor P N` — `N` is an *excluded minor* for `P`: it fails `P`
  while all its proper minors satisfy `P`;
* `IsRepresentable F M` — `M` is representable over the field `F` by vectors in
  some finite-dimensional coordinate space;
* `dual_isMinor_dual` — the minor order is compatible with matroid duality;
* `GGW_Conjecture` — the Geelen–Gerards–Whittle well-quasi-ordering statement
  for `F`-representable matroids, and `ggw_implies_finite_excluded_minors`, the
  deduction that under it every minor-closed class has only finitely many
  representable excluded minors (excluded minors form an antichain, and a
  well-quasi-order has no infinite antichain).
-/

open Set Matroid

variable {α : Type*}

/-! ## Minor-closed classes -/

/-- A property of matroids is **minor-closed** if it passes to every minor. -/
def MinorClosed (P : Matroid α → Prop) : Prop :=
  ∀ M N : Matroid α, P M → N ≤m M → P N

/-- `N` is an **excluded (forbidden) minor** for `P` if `N` fails `P` but every
proper minor of `N` satisfies `P`. -/
def IsForbiddenMinor (P : Matroid α → Prop) (N : Matroid α) : Prop :=
  ¬ P N ∧ ∀ M : Matroid α, M <m N → P M


/-! ## Duality -/


/-! ## Representability -/

/-- `M` is **representable over `F`** if its ground set can be mapped to a
finite-dimensional coordinate space over `F` so that independence in `M` is
linear independence of the corresponding vectors. -/
def IsRepresentable (F : Type*) [Field F] (M : Matroid α) : Prop :=
  ∃ (n : ℕ) (φ : α → (Fin n → F)), ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndepOn F φ I)

/-! ## Well-quasi-ordering and finiteness of excluded minors -/

/-- The **Geelen–Gerards–Whittle statement**: the matroids representable over a
finite field `F` are well-quasi-ordered by the minor order, i.e. in every
infinite sequence of representable matroids some earlier term is a minor of some
later term. -/
def GGW_Conjecture (α : Type*) (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ f : ℕ → Matroid α, (∀ i, IsRepresentable F (f i)) → ∃ i j, i < j ∧ f i ≤m f j


