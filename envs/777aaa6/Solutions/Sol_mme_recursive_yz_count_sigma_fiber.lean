-- Prove2me | solution 1 for mme_recursive_yz_count_sigma_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:12:23.916852+00:00
-- url     : https://prove2.me/submissions/b0b1d94d-c77f-44b5-98e2-0f0164296574

import Definitions.Def_mme_recursive_yz_compatibility

open MME.RecursiveYZ

/-- A cell whose label records its region counts only positions in that region. -/
theorem solution
    {R : Type*} [Fintype R] {P C : R → Type*} [∀ r, Fintype (P r)]
    {W : Type*} (cell : ∀ r, P r → C r) (f : (Σ r, P r) → W)
    (r : R) (c : C r) (w : W) :
    count (fun p : Σ r, P r => (⟨p.1, cell p.1 p.2⟩ : Σ r, C r)) f ⟨r,c⟩ w =
      count (cell r) (fun p => f ⟨r,p⟩) c w := by
  classical
  unfold count
  symm
  apply Finset.card_bij (fun p _ => (⟨r,p⟩ : Σ r, P r))
  · intro p hp
    simpa using hp
  · intro p hp q hq h
    simpa using h
  · rintro ⟨s,p⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hs : s = r := congrArg Sigma.fst hp.1
    subst s
    refine ⟨p, ?_, rfl⟩
    simpa using hp


#print axioms solution
