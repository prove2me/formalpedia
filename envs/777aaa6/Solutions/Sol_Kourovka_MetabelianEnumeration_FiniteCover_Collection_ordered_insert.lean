-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FiniteCover.Collection.ordered_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:05:11.597315+00:00
-- url     : https://prove2.me/submissions/3786c189-31d8-4211-83ef-61f262322a86

import Definitions.Def_Kourovka_Covers_FiniteCover
import Mathlib.Algebra.Group.Conj
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Subgroup.Centralizer
import Definitions.Def_Kourovka_Collection_Collection
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_zpow_mul
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_snoc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefixBudget_solid
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_prefix_mem
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_snoc_mem_of_abs_le
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FiniteCover Kourovka.MetabelianEnumeration.FiniteCover.Collection
variable {G : Type*} [Group G]
namespace Kourovka.MetabelianEnumeration.FiniteCover.Collection
theorem _root_.solution {a : ℕ} (A : Fin a → G) :
    ∀ {k : ℕ} (t : Fin k → G) (designated : Fin k → Fin k → Fin a)
      (B : Set (Lattice k)),
      Solid B →
      (∀ i j, i < j → rightComm (t i) (t j) = A (designated i j)) →
      (∀ p q v, v ∈ B → Commute (A p) (conjugate (A q) (orderedWord t v))) →
      ∀ p v i, v ∈ B → raise v i ∈ B →
        conjugate (A p) (orderedWord t v * t i) =
          conjugate (A p) (orderedWord t (raise v i)) := by
  intro k
  induction k with
  | zero =>
    intro t designated B hB ht hshort p v i
    exact Fin.elim0 i
  | succ k ih =>
    intro t designated B hB ht hshort p v i hv hvi
    obtain ⟨⟨m, w⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (k + 1) => ℤ)).surjective v
    change Fin.snoc w m ∈ B at hv
    change raise (Fin.snoc w m) i ∈ B at hvi
    change conjugate (A p) (orderedWord t (Fin.snoc w m) * t i) =
      conjugate (A p) (orderedWord t (raise (Fin.snoc w m) i))
    revert hvi
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hvi
      simp only [raise_snoc_last, orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last]
      rw [mul_assoc, ← zpow_add_one]
    · intro hvi
      rw [raise_snoc_castSucc] at hvi ⊢
      let t' : Fin k → G := fun j => t j.castSucc
      let d' : Fin k → Fin k → Fin a := fun j l => designated j.castSucc l.castSucc
      have ht' : ∀ j l, j < l → rightComm (t' j) (t' l) = A (d' j l) := by
        intro j l hjl
        exact ht j.castSucc l.castSucc hjl
      have hs' : ∀ b c v, v ∈ prefixBudget B →
          Commute (A b) (conjugate (A c) (orderedWord t' v)) := by
        intro b c v hv
        simpa [orderedWord_snoc, t'] using hshort b c (Fin.snoc v 0) hv
      have hi := ih t' d' (prefixBudget B) (prefixBudget_solid hB) ht' hs' p w i
        (prefix_mem hB hv) (prefix_mem hB hvi)
      let s := t i.castSucc
      let b := t (Fin.last k)
      let c := A (designated i.castSucc (Fin.last k))
      have hc : rightComm s b = c := ht i.castSucc (Fin.last k) i.castSucc_lt_last
      have hbc : b * c⁻¹ = s⁻¹ * b * s := by
        rw [← hc, rightComm]
        group
      have hp : b ^ m * s = s * (b * c⁻¹) ^ m := by
        rw [hbc]
        have hz : (s⁻¹ * b * s) ^ m = s⁻¹ * b ^ m * s := by
          simpa using (conj_zpow (a := s⁻¹) (b := b) (i := m))
        rw [hz]
        group
      have horbit : ∀ r : ℤ, |r| ≤ |m| →
          Commute c⁻¹ (conjugate (conjugate (A p) (orderedWord t' (raise w i))) (b ^ r)) := by
        intro r hr
        have hs := hshort (designated i.castSucc (Fin.last k)) p
          (Fin.snoc (raise w i) r) (snoc_mem_of_abs_le hB hvi hr)
        simpa only [orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last,
          conjugate_mul] using hs.inv_left
      simp only [orderedWord_snoc, Fin.snoc_castSucc, Fin.snoc_last]
      change conjugate (A p) ((orderedWord t' w * b ^ m) * s) =
        conjugate (A p) (orderedWord t' (raise w i) * b ^ m)
      rw [mul_assoc, hp, ← mul_assoc, conjugate_mul, hi]
      rw [conjugate_zpow_mul _ b c⁻¹ m horbit, conjugate_mul]
end Kourovka.MetabelianEnumeration.FiniteCover.Collection
