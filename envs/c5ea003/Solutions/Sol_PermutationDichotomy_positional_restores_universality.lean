-- Prove2me | solution 1 for PermutationDichotomy.positional_restores_universality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:18:44.524195+00:00
-- url     : https://prove2.me/submissions/625ad2f1-074e-4049-9617-326aae0e5353

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy
import Theorems.Thm_PermutationDichotomy_attentionAlgebra_separatesPoints
import Theorems.Thm_PermutationDichotomy_symmetrize_error
import Theorems.Thm_PermutationDichotomy_continuous_decodeSeq
set_option autoImplicit false
open scoped BigOperators
open PermutationDichotomy
namespace QuickPositional
variable {ι κ : Type*}
theorem permAct_comp (σ τ : Equiv.Perm ι) (x : Seq ι κ) :
    permAct σ (permAct τ x) = permAct (τ * σ) x := rfl
variable [Fintype ι] [Fintype κ]
theorem readout_mem_attentionAlgebra (w : Seq ι κ) : readoutCM w ∈ attentionAlgebra ι κ :=
  Algebra.subset_adjoin ⟨w, rfl⟩
theorem readoutCM_comp_permCM (σ : Equiv.Perm ι) (w : Seq ι κ) :
    (ContinuousMap.compRightAlgHom ℝ ℝ (permCM σ)) (readoutCM w)
      = readoutCM (fun i a => w (σ.symm i) a) := by
  ext x
  show ∑ i, ∑ a, w i a * x (σ i) a = ∑ i, ∑ a, w (σ.symm i) a * x i a
  rw [← Equiv.sum_comp σ (fun j => ∑ a, w (σ.symm j) a * x j a)]
  simp

/-- **The architecture class is stable under the token-permutation action.** -/
theorem attentionAlgebra_compPerm_mem (σ : Equiv.Perm ι) {p : C(Seq ι κ, ℝ)}
    (hp : p ∈ attentionAlgebra ι κ) :
    (ContinuousMap.compRightAlgHom ℝ ℝ (permCM σ)) p ∈ attentionAlgebra ι κ := by
  have hsub :
      attentionAlgebra ι κ ≤
        (attentionAlgebra ι κ).comap (ContinuousMap.compRightAlgHom ℝ ℝ (permCM σ)) := by
    apply Algebra.adjoin_le
    rintro _ ⟨w, rfl⟩
    show (ContinuousMap.compRightAlgHom ℝ ℝ (permCM σ)) (readoutCM w) ∈ attentionAlgebra ι κ
    rw [readoutCM_comp_permCM]
    exact readout_mem_attentionAlgebra _
  exact hsub hp

variable {Γ : Type*} [Group Γ] [Fintype Γ]
theorem symmetrize_apply (act : Γ →* Equiv.Perm ι) (q : C(Seq ι κ, ℝ)) (x : Seq ι κ) :
    symmetrize act q x = (Fintype.card Γ : ℝ)⁻¹ * ∑ g : Γ, q (permAct (act g) x) := by
  simp [symmetrize, permCM]
theorem symmetrize_mem (act : Γ →* Equiv.Perm ι) {q : C(Seq ι κ, ℝ)}
    (hq : q ∈ attentionAlgebra ι κ) :
    symmetrize act q ∈ attentionAlgebra ι κ :=
  Subalgebra.smul_mem _
    (Subalgebra.sum_mem _ fun g _ => attentionAlgebra_compPerm_mem (act g) hq) _
theorem symmetrize_invariant (act : Γ →* Equiv.Perm ι) (q : C(Seq ι κ, ℝ)) :
    InvariantUnder act (fun x => symmetrize act q x) := by
  intro tau x
  simp only [symmetrize_apply]
  apply congrArg (fun t : ℝ => (Fintype.card Γ : ℝ)⁻¹ * t)
  rw [← Equiv.sum_comp (Equiv.mulLeft tau) (fun rho : Γ => q (permAct (act rho) x))]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [permAct_comp, ← MonoidHom.map_mul]
  rfl
theorem group_uniform_universal (act : Γ →* Equiv.Perm ι) (g : C(Seq ι κ, ℝ))
    (hg : InvariantUnder act (fun x => g x)) {K : Set (Seq ι κ)} (hK : IsCompact K)
    (hKsat : SaturatedUnder act K) {eps : ℝ} (heps : 0 < eps) :
    ∃ p ∈ attentionAlgebra ι κ,
      InvariantUnder act (fun x => p x) ∧ ∀ x ∈ K, |p x - g x| < eps := by
  obtain ⟨q, hq, hclose⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      (A := attentionAlgebra ι κ) attentionAlgebra_separatesPoints g hK heps
  refine ⟨symmetrize act q, symmetrize_mem act hq, symmetrize_invariant act q, ?_⟩
  refine symmetrize_error act hg hKsat ?_
  intro x hx
  simpa [Real.norm_eq_abs] using hclose x hx

variable [DecidableEq ι]

/-- **Full permutation symmetry.**  Specialization of `group_uniform_universal` to the whole
symmetric group: a positional-encoding-free attention architecture uniformly approximates
exactly the permutation-invariant continuous functionals. -/
theorem symmetric_uniform_universal (g : C(Seq ι κ, ℝ)) (hg : Invariant (fun x => g x))
    {K : Set (Seq ι κ)} (hK : IsCompact K) (hKsat : Saturated K) {eps : ℝ} (heps : 0 < eps) :
    ∃ p ∈ attentionAlgebra ι κ,
      Invariant (fun x => p x) ∧ ∀ x ∈ K, |p x - g x| < eps :=
  group_uniform_universal (MonoidHom.id (Equiv.Perm ι)) g hg hK hKsat heps
theorem continuous_posEnc : Continuous (posEnc (ι := ι) (κ := κ)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro c
  cases c with
  | inl a => exact (continuous_apply a).comp (continuous_apply i)
  | inr j => exact continuous_const
theorem decodeSeq_posEnc (x : Seq ι κ) : decodeSeq (posEnc x) = x := by
  funext i a
  show ∑ j, (if i = j then (1:ℝ) else 0) * x j a = x i a
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **The decoder is permutation invariant**, so any functional built through it is invariant. -/
theorem decodeSeq_invariant (σ : Equiv.Perm ι) (z : Seq ι (κ ⊕ ι)) :
    decodeSeq (permAct σ z) = decodeSeq z := by
  funext i a
  show ∑ j, z (σ j) (Sum.inr i) * z (σ j) (Sum.inl a)
      = ∑ j, z j (Sum.inr i) * z j (Sum.inl a)
  exact Equiv.sum_comp σ (fun j => z j (Sum.inr i) * z j (Sum.inl a))
theorem posEnc_mem_encSaturation {K : Set (Seq ι κ)} {x : Seq ι κ} (hx : x ∈ K) :
    posEnc x ∈ encSaturation K :=
  Set.mem_iUnion.mpr ⟨1, ⟨posEnc x, ⟨x, hx, rfl⟩, rfl⟩⟩

theorem isCompact_encSaturation {K : Set (Seq ι κ)} (hK : IsCompact K) :
    IsCompact (encSaturation K) :=
  isCompact_iUnion fun σ =>
    ((hK.image continuous_posEnc).image (continuous_permAct σ))

theorem saturated_encSaturation (K : Set (Seq ι κ)) : Saturated (encSaturation K) := by
  rintro tau z hz
  rw [encSaturation, Set.mem_iUnion] at hz ⊢
  obtain ⟨σ, w, hw, rfl⟩ := hz
  exact ⟨σ * tau, w, hw, (permAct_comp tau σ w).symm ▸ rfl⟩
end QuickPositional
open QuickPositional
theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : C(Seq ι κ, ℝ)) {K : Set (Seq ι κ)}
    (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ p ∈ attentionAlgebra ι (κ ⊕ ι),
      Invariant (fun z => p z) ∧ ∀ x ∈ K, |p (posEnc x) - g x| < eps := by
  set G : C(Seq ι (κ ⊕ ι), ℝ) := g.comp ⟨decodeSeq, continuous_decodeSeq⟩ with hG
  have hGinv : Invariant (fun z => G z) := by
    intro σ z
    show g (decodeSeq (permAct σ z)) = g (decodeSeq z)
    rw [decodeSeq_invariant]
  obtain ⟨p, hp, hpinv, hclose⟩ :=
    symmetric_uniform_universal (ι := ι) (κ := κ ⊕ ι) G hGinv
      (isCompact_encSaturation hK) (saturated_encSaturation K) heps
  refine ⟨p, hp, hpinv, ?_⟩
  intro x hx
  have := hclose (posEnc x) (posEnc_mem_encSaturation hx)
  have hGx : G (posEnc x) = g x := by
    show g (decodeSeq (posEnc x)) = g x
    rw [decodeSeq_posEnc]
  rwa [hGx] at this

#print axioms solution
