-- Prove2me | solution 1 for dual_isMinor_dual
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:23:28.151195+00:00
-- url     : https://prove2.me/submissions/3621656a-c63d-4aa4-98a0-4d9a654bd827

-- Sol generated from Applications/PosetTheory/MatroidMinorBasic.lean
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



theorem solution{M N : Matroid α} (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, -, -, hCD, rfl⟩ := h.exists_eq_contract_delete_disjoint
  rw [Matroid.dual_contract_delete, ← Matroid.contract_delete_comm _ hCD.symm]
  exact ⟨D, C, rfl⟩
