-- Prove2me | solution 1 for mme_CW_q6_common_halving_fiber_paired_support_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T04:33:37.092841+00:00
-- url     : https://prove2.me/submissions/3317e62b-0f26-4e39-9cf4-4bfbad57c629

import Definitions.Def_mme_CW_q6_paired_cyclic_induced

open MME
set_option autoImplicit false

private theorem coupled_cross_support_iff {x y x' y' z : Fin 3}
    (h : CWQ6CoupledLocalSupported x y z)
    (h' : CWQ6CoupledLocalSupported x' y' z) :
    CWQ6CoupledLocalSupported x y' z ↔ x = x' ∧ y = y' := by
  rcases h with h | h | h | h <;>
    rcases h' with h' | h' | h' | h' <;>
    simp_all [CWQ6CoupledLocalSupported]

/-- Within a color, the mixed paired support is determined exactly by the
first X half of the first and third entries and the second Y half of the
second and third entries. -/
theorem solution
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (a : Fin A)
    (h0 h1 h2 : Fin H) :
    family.PairedCyclicSupported halving (a,h0) (a,h1) (a,h2) ↔
      (∀ r : Fin N, (family.entry (a,h0)).val 0 (halving.position (Sum.inl r)) =
        (family.entry (a,h2)).val 0 (halving.position (Sum.inl r))) ∧
      (∀ r : Fin N, (family.entry (a,h1)).val 1 (halving.position (Sum.inr r)) =
        (family.entry (a,h2)).val 1 (halving.position (Sum.inr r))) := by
  have hz (h : Fin H) (j : Fin (2 * N)) :
      (family.entry (a,h)).val 2 j = (family.entry (a,h2)).val 2 j :=
    congrFun (family.zSameFiber a h h2) j
  have he (h : Fin H) (j : Fin (2 * N)) :
      CWQ6CoupledLocalSupported ((family.entry (a,h)).val 0 j)
        ((family.entry (a,h)).val 1 j) ((family.entry (a,h2)).val 2 j) := by
    have hs := (family.entry (a,h)).property.1 j
    change CWQ6CoupledLocalSupported _ _ _ at hs
    simpa only [hz] using hs
  unfold CWQ6PrimaryHashFamily.PairedCyclicSupported
  simp only [hz]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun r ↦ ((coupled_cross_support_iff (he h2 _) (he h0 _)).mp (hl r)).1.symm,
      fun r ↦ ((coupled_cross_support_iff (he h1 _) (he h2 _)).mp (hr r)).2⟩
  · rintro ⟨hl, hr⟩
    constructor
    · intro r
      rw [← hl r]
      exact he h0 _
    · intro r
      rw [← hr r]
      exact he h1 _


#print axioms solution
