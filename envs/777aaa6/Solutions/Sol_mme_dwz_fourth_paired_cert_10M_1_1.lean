-- Prove2me | solution 1 for mme_dwz_fourth_paired_cert_10M_1_1
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-20T23:39:59.901855+00:00
-- url     : https://prove2.me/submissions/ddd34be4-56da-4a25-97b8-0196b3df4d2d

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_flattening
import Definitions.Def_mme_rank_bridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic
import Mathlib.Algebra.Field.ULift

open MME PiTensorProduct TensorProduct Module BigOperators
universe u
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 200000

namespace TensorCertificateAudit
variable {K : Type u} [Field K]

-- Direct coordinate projection, adapted from Def_mme_omega_normalize's scalar base case.
theorem one_restrict_MM111 :
    TensorObj.Restrict (TensorObj.oneObj : TensorObj K 3) (MMObj K 1 1 1) := by
  let toOne : ∀ s : Fin 3, (MMObj K 1 1 1).V s →ₗ[K]
      (TensorObj.oneObj : TensorObj K 3).V s :=
    fun s => Fin.cases (LinearMap.proj (0, 0))
      (fun s => Fin.cases (LinearMap.proj (0, 0))
        (fun s => Fin.cases (LinearMap.proj (0, 0))
          (fun s => absurd s.isLt (by omega)) s) s) s
  refine ⟨toOne, ?_⟩
  change PiTensorProduct.map toOne (MMTensor K 1 1 1) = tprod K (fun _ => (1 : K))
  simp only [MMTensor, Fin.sum_univ_one]
  erw [PiTensorProduct.map_tprod]
  congr 1
  funext s
  fin_cases s <;>
    change (LinearMap.proj (0, 0)) (Pi.single (0, 0) 1 : Fin 1 × Fin 1 → K) = 1 <;>
    rw [LinearMap.proj_apply, Pi.single_eq_same]

theorem one_restrict_star {T : TensorObj K 3}
    (cert : CTensorOneHOneCertificate T 1 1) :
    TensorObj.Restrict TensorObj.oneObj T := by
  have hv := cert.common_volume 0
  have hm : cert.m 0 = 1 := Nat.eq_one_of_mul_eq_one_right (Nat.eq_one_of_mul_eq_one_right hv)
  have hn : cert.n 0 = 1 := Nat.eq_one_of_mul_eq_one_left (Nat.eq_one_of_mul_eq_one_right hv)
  have hp : cert.p 0 = 1 := Nat.eq_one_of_mul_eq_one_left hv
  have hc := (cert.component 0).1
  rw [hm, hn, hp] at hc
  have hb : TensorObj.Restrict
      (cert.grading.blockSubtensor (cTensorOneHOneAddress 1 0)) T :=
    ⟨fun i => cert.grading.blockProj i (cTensorOneHOneAddress 1 0 i), rfl⟩
  exact one_restrict_MM111.trans (hc.trans hb)

-- The accepted proof of bigAdd monotonicity is inserted ahead of the remaining lemmas.
namespace BigAddMonoRestrict

theorem add_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hf : TensorObj.Restrict X X') (hg : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.add X Y) (TensorObj.add X' Y') := by
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := hg
  refine ⟨fun i => LinearMap.prodMap (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => LinearMap.prodMap (f i) (g i))
      (PiTensorProduct.map (fun i => LinearMap.inl K (X'.V i) (Y'.V i)) X'.t +
       PiTensorProduct.map (fun i => LinearMap.inr K (X'.V i) (Y'.V i)) Y'.t) =
      PiTensorProduct.map (fun i => LinearMap.inl K (X.V i) (Y.V i)) X.t +
      PiTensorProduct.map (fun i => LinearMap.inr K (X.V i) (Y.V i)) Y.t
  have h1 :
      (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ
        LinearMap.inl K (X'.V i) (Y'.V i)) =
      (fun i => LinearMap.inl K (X.V i) (Y.V i) ∘ₗ f i) := by
    funext i
    ext x <;> simp [LinearMap.prodMap]
  have h2 :
      (fun i => LinearMap.prodMap (f i) (g i) ∘ₗ
        LinearMap.inr K (X'.V i) (Y'.V i)) =
      (fun i => LinearMap.inr K (X.V i) (Y.V i) ∘ₗ g i) := by
    funext i
    ext x <;> simp [LinearMap.prodMap]
  rw [map_add, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp, h1, h2,
    PiTensorProduct.map_comp, PiTensorProduct.map_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]

end BigAddMonoRestrict

theorem bigAdd_mono_restrict
    {K : Type u} [Field K] {d k : ℕ}
    {X Y : Fin k → TensorObj K d}
    (h : ∀ j, TensorObj.Restrict (X j) (Y j)) :
    TensorObj.Restrict (TensorObj.bigAdd X) (TensorObj.bigAdd Y) := by
  induction k with
  | zero => exact TensorObj.Restrict.refl _
  | succ k ih =>
    cases k with
    | zero =>
      change TensorObj.Restrict (X 0) (Y 0)
      exact h 0
    | succ k =>
      change TensorObj.Restrict
        (TensorObj.add (X 0) (TensorObj.bigAdd (fun i => X i.succ)))
        (TensorObj.add (Y 0) (TensorObj.bigAdd (fun i => Y i.succ)))
      exact BigAddMonoRestrict.add_restrict (h 0)
        (ih (X := fun i => X i.succ) (Y := fun i => Y i.succ)
          (fun i => h i.succ))

theorem diag_restrict_of_certificate {T : TensorObj K 3} {A : ℕ}
    (cert : CTensorOneHOneFamilyCertificate T A 1 1) :
    TensorObj.Restrict (TensorObj.diagObj K 3 A) T := by
  have hsum : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin A => (TensorObj.oneObj : TensorObj K 3)))
      (TensorObj.bigAdd cert.star) :=
    bigAdd_mono_restrict (fun a => one_restrict_star (cert.certificate a))
  have heq : TensorQ.toQ (TensorObj.diagObj K 3 A) =
      TensorQ.toQ (TensorObj.bigAdd (fun _ : Fin A =>
        (TensorObj.oneObj : TensorObj K 3))) := by
    rw [TensorQ.toQ_bigAdd, ← TensorQ.natCast_eq]
    simp only [← TensorQ.toQ_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  exact (TensorQ.toQ_eq_iff.mp heq).1.trans (hsum.trans cert.restrict)

abbrev FourthIndex := (Fin 7 × Fin 7) × (Fin 7 × Fin 7)
abbrev PairedIndex := FourthIndex × FourthIndex
noncomputable def source (K : Type u) [Field K] : TensorObj K 3 :=
  TensorObj.kron (MME.StothersFourth.cwFourthObj K 5)
    (TensorObj.permObj MME.swapFirstTwoPerm (MME.StothersFourth.cwFourthObj K 5))

noncomputable def sourceBasis (s : Fin 3) : Basis PairedIndex K ((source K).V s) :=
  Module.Basis.tensorProduct
    (MME.StothersFourth.cwFourthCanonicalBasis K 5 s)
    (MME.StothersFourth.cwFourthCanonicalBasis K 5 (MME.swapFirstTwoPerm.symm s))

theorem uniform_basis_flatteningRank_le {I : Type*} [Fintype I]
    (X : TensorObj K 3) (basis : ∀ s, Basis I K (X.V s)) :
    flatteningRank (diagSplit (d := 3) (by norm_num)) X ≤ Fintype.card I := by
  classical
  let σ : Split (Fin 3) := diagSplit (by norm_num)
  change Module.finrank K (LinearMap.range (flatteningMap σ X)) ≤ Fintype.card I
  let b := Basis.piTensorProduct (fun i : σ.S => basis i.val)
  haveI : Module.Finite K (PiTensorProduct K (fun i : σ.S => X.V i)) :=
    Module.Finite.of_basis b
  calc
    Module.finrank K (LinearMap.range (flatteningMap σ X)) ≤
        Module.finrank K (Module.Dual K (PiTensorProduct K (fun i : σ.S => X.V i))) :=
      LinearMap.finrank_range_le (flatteningMap σ X)
    _ = Module.finrank K (PiTensorProduct K (fun i : σ.S => X.V i)) :=
      Subspace.dual_finrank_eq
    _ = Fintype.card I := by
      rw [Module.finrank_eq_card_basis b]
      simp [σ, diagSplit, Fintype.card_fun]

theorem source_flatteningRank_le :
    flatteningRank (diagSplit (d := 3) (by norm_num)) (source K) ≤ 5764801 := by
  have h := uniform_basis_flatteningRank_le (source K) (sourceBasis (K := K))
  norm_num [PairedIndex, FourthIndex] at h
  exact h

theorem certificate_impossible :
    ¬ Nonempty (CTensorOneHOneFamilyCertificate (source K) 10000000 1 1) := by
  rintro ⟨cert⟩
  have h := flatteningRank_mono (diagSplit (d := 3) (by norm_num))
    (diag_restrict_of_certificate cert)
  rw [flatteningRank_diag] at h
  have hdim := source_flatteningRank_le (K := K)
  omega
end TensorCertificateAudit

theorem solution :
    ¬ (∀ (K : Type) [Field K],
      Nonempty (CTensorOneHOneFamilyCertificate
        (TensorObj.kron (MME.StothersFourth.cwFourthObj K 5)
          (TensorObj.permObj MME.swapFirstTwoPerm (MME.StothersFourth.cwFourthObj K 5)))
        10000000 1 1)) := by
  intro h
  exact TensorCertificateAudit.certificate_impossible (K := ℚ) (h _)

#print axioms TensorCertificateAudit.diag_restrict_of_certificate
#print axioms TensorCertificateAudit.source_flatteningRank_le
#print axioms TensorCertificateAudit.certificate_impossible
#print axioms solution
