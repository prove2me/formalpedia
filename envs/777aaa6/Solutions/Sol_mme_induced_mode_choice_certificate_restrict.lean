-- Prove2me | solution 1 for mme_induced_mode_choice_certificate_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:48:59.727577+00:00
-- url     : https://prove2.me/submissions/38ba9f0e-544e-4cee-84bc-24d5cdb5b60c

import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_tensor_quotient

open MME PiTensorProduct BigOperators

universe u

namespace InducedModeChoiceCertificateRestrict

/-- Tensoring a finite sum of maps in each of three modes expands over all
triples of summand choices. -/
theorem map_sum_modes
    {K : Type u} [Field K]
    {slotCount : Fin 3 → ℕ}
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin (slotCount i) → V i →ₗ[K] W i)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i => ∑ j, f i j) x =
      ∑ choice : ∀ i : Fin 3, Fin (slotCount i),
        PiTensorProduct.map (fun i => f i (choice i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      simp only [map_smul]
      simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum,
        Finset.sum_apply]
      rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _]
      rw [Finset.smul_sum]
  | add x y ihx ihy =>
      simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

end InducedModeChoiceCertificateRestrict

/-- Every finite induced mode-choice certificate gives the claimed tensor
restriction by summing its mode maps. -/
theorem solution
    {K : Type u} [Field K]
    {source target : TensorObj K 3}
    (cert : InducedModeChoiceCertificate source target) :
    TensorObj.Restrict target source := by
  classical
  refine ⟨fun i => ∑ j, cert.modeMap i j, ?_⟩
  rw [InducedModeChoiceCertificateRestrict.map_sum_modes]
  have hsubset : cert.kept ⊆ Finset.univ := Finset.subset_univ _
  have hkept :
      (∑ choice ∈ cert.kept,
        PiTensorProduct.map
          (fun i => cert.modeMap i (choice i)) source.t) =
      ∑ choice : ∀ i : Fin 3, Fin (cert.slotCount i),
        PiTensorProduct.map
          (fun i => cert.modeMap i (choice i)) source.t := by
    exact Finset.sum_subset hsubset (fun choice _ hnot =>
      cert.offSupport choice hnot)
  rw [← hkept]
  rw [cert.targetTensor]
  simpa only [Finset.attach_eq_univ] using
    (Finset.sum_attach cert.kept
      (fun choice =>
        PiTensorProduct.map
          (fun i => cert.modeMap i (choice i)) source.t)).symm
