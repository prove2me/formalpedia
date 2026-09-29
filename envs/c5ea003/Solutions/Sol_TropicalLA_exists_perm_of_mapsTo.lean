-- Prove2me | solution 1 for TropicalLA.exists_perm_of_mapsTo
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T04:07:17.741355+00:00
-- url     : https://prove2.me/submissions/586dd4ce-77ee-4555-8c05-9bd391abbb43

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalEigenvalue
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {s : Finset ι} {f : ι → ι}
    (hmaps : ∀ i ∈ s, f i ∈ s) (hinj : Set.InjOn f s) :
    ∃ σ : Equiv.Perm ι, ∀ i ∈ s, σ i = f i := by
  classical
  -- an injective self-map of a finite set is a bijection of it
  have hbij : Set.BijOn f (s : Set ι) (s : Set ι) :=
    (Set.Finite.injOn_iff_bijOn_of_mapsTo s.finite_toSet (fun i hi => hmaps i hi)).mp hinj
  -- extend it by the identity outside `s`
  refine ⟨Equiv.Perm.ofSubtype (hbij.equiv f), fun i hi => ?_⟩
  rw [Equiv.Perm.ofSubtype_apply_of_mem _ (show i ∈ (s : Set ι) from hi)]
  rfl
