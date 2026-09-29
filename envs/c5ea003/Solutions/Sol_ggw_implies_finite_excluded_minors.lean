-- Prove2me | solution 1 for ggw_implies_finite_excluded_minors
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:23:28.615735+00:00
-- url     : https://prove2.me/submissions/e62501fe-c66f-4c7c-85c1-0213289288b7

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



/-- Excluded minors form an **antichain** in the minor order: two distinct
excluded minors are incomparable. -/
theorem not_isMinor_of_isForbiddenMinor {P : Matroid α → Prop} {M N : Matroid α}
    (hM : IsForbiddenMinor P M) (hN : IsForbiddenMinor P N) (hne : M ≠ N) : ¬ M ≤m N := by
  intro hle
  have hstrict : M <m N := ⟨hle, fun hge => hne (Matroid.IsMinor.antisymm hle hge)⟩
  exact hM.1 (hN.2 M hstrict)

/-! ## Duality -/


/-! ## Representability -/


/-! ## Well-quasi-ordering and finiteness of excluded minors -/



theorem solution(F : Type*) [Field F] [Fintype F]
    (hGGW : GGW_Conjecture α F) (P : Matroid α → Prop) (_hP : MinorClosed P) :
    Set.Finite {N : Matroid α | IsRepresentable F N ∧ IsForbiddenMinor P N} := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨e⟩ : Nonempty (ℕ ↪ {N : Matroid α | IsRepresentable F N ∧ IsForbiddenMinor P N}) :=
    ⟨hinf.natEmbedding⟩
  set f : ℕ → Matroid α := fun i => (e i : Matroid α) with hf
  have hmem : ∀ i, IsRepresentable F (f i) ∧ IsForbiddenMinor P (f i) := fun i => (e i).2
  obtain ⟨i, j, hij, hle⟩ := hGGW f (fun i => (hmem i).1)
  have hne : f i ≠ f j := by
    intro h
    exact absurd (e.injective (Subtype.ext h)) (Nat.ne_of_lt hij)
  exact not_isMinor_of_isForbiddenMinor (hmem i).2 (hmem j).2 hne hle
