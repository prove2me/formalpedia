-- Prove2me | solution 1 for mme_profiled_CW_regroup_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T09:58:33.390876+00:00
-- url     : https://prove2.me/submissions/94e944a1-9918-4097-8cb8-e817fe1a39d8

import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_profiled_CW_joint_projection_restrict

open MME MME.TensorObj MME.ProfiledCW
universe u

/-- Regrouping elementary coordinates preserves a product restriction whenever
all target region predicates imply the source part predicates. The implication
uses one common tensor mode throughout the coordinate partition. -/
theorem solution {K : Type u} [Field K]
    {a b : ℕ} (sizeA : Fin a → ℕ) (sizeB : Fin b → ℕ)
    (e : (Σ j : Fin a, Fin (sizeA j)) ≃ (Σ r : Fin b, Fin (sizeB r)))
    (P : ∀ j, Predicate (sizeA j)) (Q : ∀ r, Predicate (sizeB r))
    (inside : ∀ i (x : ∀ r, FineWord (sizeB r)),
      (∀ r, Q r i (x r)) →
        ∀ j, P j i (fun q => x (e ⟨j,q⟩).1 (e ⟨j,q⟩).2)) :
    Restrict (kronFin b (fun r => tensor K (Q r)))
      (kronFin a (fun j => tensor K (P j))) := by
  classical
  let positions := Fintype.equivFin (Σ r : Fin b, Fin (sizeB r))
  let G : Predicate (Fintype.card (Σ r : Fin b, Fin (sizeB r))) :=
    fun i x => ∀ r, Q r i (fun q => x (positions ⟨r,q⟩))
  have hregions : Restrict (kronFin b (fun r => tensor K (Q r))) (tensor K G) :=
    mme_profiled_CW_region_product_restrict G sizeB positions Q (fun _ _ h => h)
  have hparts : Restrict (tensor K G) (kronFin a (fun j => tensor K (P j))) := by
    apply mme_profiled_CW_joint_projection_restrict sizeA (e.trans positions) P G
    intro i x hx j
    exact inside i (fun r q => x (positions ⟨r,q⟩)) hx j
  exact hregions.trans hparts


#print axioms solution
