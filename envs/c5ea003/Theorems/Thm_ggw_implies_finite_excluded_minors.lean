-- Prove2me | Theorems.Thm_ggw_implies_finite_excluded_minors
-- name    : ggw_implies_finite_excluded_minors
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:43.475488+00:00
-- url     : https://prove2.me/theorems/5ef6b571-7597-444e-bd07-6417fe477982
-- title:
--   From well-quasi-ordering to finitely many excluded minors.
-- statement:
--   **From well-quasi-ordering to finitely many excluded minors.**
--
--   If the `F`-representable matroids are well-quasi-ordered by the minor relation,
--   then for every property `P` there are only finitely many representable excluded
--   minors for `P`: they form an antichain, and an infinite antichain would give an
--   infinite sequence violating the well-quasi-ordering.
--
--   (The minor-closedness hypothesis `_hP` is recorded because it is part of the
--   usual statement, but the antichain argument does not need it.)
--
--   ```lean
--   theorem ggw_implies_finite_excluded_minors(F : Type*) [Field F] [Fintype F]
--       (hGGW : GGW_Conjecture α F) (P : Matroid α → Prop) (_hP : MinorClosed P) :
--       Set.Finite {N : Matroid α | IsRepresentable F N ∧ IsForbiddenMinor P N} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PosetTheory/MatroidMinorBasic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PosetTheory/MatroidMinorBasic.lean#L70

-- Thm stub generated from Applications/PosetTheory/MatroidMinorBasic.lean
import Mathlib
import Definitions.Def_Applications_PosetTheory_MatroidMinorBasic

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




/-! ## Duality -/


/-! ## Representability -/


/-! ## Well-quasi-ordering and finiteness of excluded minors -/

theorem ggw_implies_finite_excluded_minors(F : Type*) [Field F] [Fintype F]
    (hGGW : GGW_Conjecture α F) (P : Matroid α → Prop) (_hP : MinorClosed P) :
    Set.Finite {N : Matroid α | IsRepresentable F N ∧ IsForbiddenMinor P N} := by sorry
