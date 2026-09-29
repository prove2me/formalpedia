-- Prove2me | solution 1 for Geometry.KernelPatterns.card_chambers
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:19.758989+00:00
-- url     : https://prove2.me/submissions/9042017b-7a85-4da2-b48d-ccd1226ba11b

-- Sol generated from Geometry/KernelPatterns/Chambers.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Chambers
import Theorems.Thm_Geometry_KernelPatterns_chamber_disjoint

/-!
# Cycle 2: chambers of the braid arrangement

The kernel pattern of a tuple records *which* coordinates coincide; on the
complement of the braid arrangement — the injective tuples — nothing coincides
and the relevant invariant becomes the *ordering* of the coordinates.  This
file is the chamber-level companion of the flat-level results in
`Geometry.KernelPatterns.BraidFlats`.

* `chamber n σ` — the open cone `v (σ 0) < v (σ 1) < ⋯ < v (σ (n-1))`.
* `chamber_convex`, `chamber_nonempty` — chambers are nonempty convex (hence
  connected) sets.
* `chamber_eq_chamber_iff`, `chamber_injective` — a chamber determines its
  permutation, i.e. the ordering is a complete invariant of the chamber.
* `iUnion_chamber` — the chambers cover exactly the complement of the
  arrangement.
* `card_chambers` — there are `n !` chambers, whereas
  (`card_braidFlats_eq_bell`) there are `Nat.bell n` flats.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}




/-- Every chamber is nonempty. -/
theorem chamber_nonempty (σ : Equiv.Perm (Fin n)) : (chamber n σ).Nonempty := by
  refine ⟨fun x => ((σ.symm x : Fin n) : ℕ), fun i j hij => ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact_mod_cast Fin.lt_def.1 hij





/-- The chamber determines the permutation. -/
theorem chamber_injective (n : ℕ) : Function.Injective (chamber n) := by
  intro σ τ h
  by_contra hne
  have hdisj := chamber_disjoint hne
  obtain ⟨v, hv⟩ := chamber_nonempty σ
  have hv' : v ∈ chamber n τ := h ▸ hv
  exact (Set.disjoint_left.1 hdisj hv) hv'




open Geometry.KernelPatterns in
theorem solution(n : ℕ) : Nat.card (chambers n) = Nat.factorial n := by
  have h : Nat.card ↥(chambers n) = Nat.card (Equiv.Perm (Fin n)) :=
    Nat.card_range_of_injective (chamber_injective n)
  rw [h, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
