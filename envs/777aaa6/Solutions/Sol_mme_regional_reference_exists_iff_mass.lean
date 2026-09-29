-- Prove2me | solution 1 for mme_regional_reference_exists_iff_mass
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:29:48.461438+00:00
-- url     : https://prove2.me/submissions/f36d6c4b-a8f5-41bb-8790-11cc6b12ae23

import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false

/-- Exact split histograms are realizable precisely when each regional mass
matches its number of physical positions. -/
theorem solution
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

#print axioms solution
