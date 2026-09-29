-- Prove2me | solution 1 for mme_released_116_scaled_reference_exists
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:35:50.465189+00:00
-- url     : https://prove2.me/submissions/a02969e6-0abc-463d-a93d-e5a166bf25b1

import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false

/-- Exact split histograms are realizable precisely when each regional mass
matches its number of physical positions. -/
theorem mme_regional_reference_exists_iff_mass
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    (∃ a : Address half R parent n, a ∈ target m) ↔
      ∀ r, ∑ c, m r c = n r := by
  classical
  constructor
  · rintro ⟨a, ha⟩ r
    have hc := (Finset.mem_filter.mp ha).2 r
    change ∀ c, count (a r) c = m r c at hc
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (n r))) Finset.univ (a r)
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] at hsum
    change (∑ c, count (a r) c) = n r at hsum
    simpa only [hc] using hsum
  · intro hmass
    let e (r : Fin R) : Fin (n r) ≃ Σ c, Fin (m r c) :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, Fintype.card_sigma]
        simpa only [Fintype.card_fin] using (hmass r).symm)
    let a : Address half R parent n := fun r t => (e r t).1
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro r c
    rw [count, ← Fintype.card_subtype]
    let ef : {t : Fin (n r) // a r t = c} ≃
        {p : (Σ c, Fin (m r c)) // p.1 = c} :=
      Equiv.subtypeEquiv (e r) (fun _ => Iff.rfl)
    rw [Fintype.card_congr ef, Fintype.card_congr (Equiv.sigmaSubtype c),
      Fintype.card_fin]


open MME.Released116 MME.MoreAsymmetryExactSeed

/-- All integer multiples of the released regional split histograms admit
physical reference assignments, including the empty scaling. -/
theorem solution (k : ℕ) :
    ∃ a : Address 4 6 parent (fun r => k * regionalSize r),
      a ∈ target (fun r c => k * splitCount r c) := by
  apply (mme_regional_reference_exists_iff_mass _).mpr
  intro r
  rw [← Finset.mul_sum]
  simpa only [parent] using
    congrArg (fun x : ℕ => k * x) (mme_released_116_regional_split_mass r).2

#print axioms solution
