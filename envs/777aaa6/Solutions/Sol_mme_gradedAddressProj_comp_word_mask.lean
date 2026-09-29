-- Prove2me | solution 1 for mme_gradedAddressProj_comp_word_mask
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T05:46:48.224549+00:00
-- url     : https://prove2.me/submissions/8bd12d9f-7095-4267-9b53-127b5b4649fa

import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch

open MME MME.DWZComponentRestriction Module
universe u
set_option autoImplicit false

/-- An address projection is unchanged by a word mask that retains every word
whose grades match the address. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) (grade : ι → Fin t)
    (hzero : ∀ (a : Fin t) (j : ι), grade j ≠ a → G.blockProj i a (b j) = 0)
    (address : Fin 3 → Fin N → Fin t)
    (keep : PowIndex ι N → Prop) [DecidablePred keep]
    (hkeep : ∀ w, (∀ r, grade (PowIndex.get N w r) = address i r) → keep w) :
    (gradedAddressProj G N address i).comp
        ((kronPowModeBasis T i b N).constr K
          (fun w => if keep w then kronPowModeBasis T i b N w else 0)) =
      gradedAddressProj G N address i := by
  classical
  apply (kronPowModeBasis T i b N).ext
  intro w
  simp only [LinearMap.comp_apply, Basis.constr_basis]
  by_cases hw : keep w
  · rw [if_pos hw]
  · rw [if_neg hw, map_zero]
    symm
    apply mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch G i b grade hzero N address w
    by_contra h
    apply hw
    apply hkeep
    intro r
    by_contra hr
    exact h ⟨r, hr⟩

#print axioms solution
