-- Prove2me | solution 1 for PermutationDichotomy.shift_uniform_universal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:18:45.629342+00:00
-- url     : https://prove2.me/submissions/e587ca09-2269-4ddd-be92-5bdfb4421ee3

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

end QuickPositional
open QuickPositional
theorem solution {ι κ : Type*} [Fintype ι] [Fintype κ] (r : Equiv.Perm ι) (g : C(Seq ι κ, ℝ))
    (hg : ∀ (k : ℕ) (x : Seq ι κ), g (permAct (r ^ k) x) = g x)
    {K : Set (Seq ι κ)} (hK : IsCompact K)
    (hKsat : ∀ k : ℕ, ∀ x ∈ K, permAct (r ^ k) x ∈ K) {eps : ℝ} (heps : 0 < eps) :
    ∃ p ∈ attentionAlgebra ι κ,
      (∀ (k : ℕ) (x : Seq ι κ), p (permAct (r ^ k) x) = p x) ∧ ∀ x ∈ K, |p x - g x| < eps := by
  classical
  haveI : Fintype (Subgroup.zpowers r) := Fintype.ofFinite _
  have hpow : ∀ s : Subgroup.zpowers r, ∃ k : ℕ, r ^ k = (s : Equiv.Perm ι) := by
    intro s
    have hs : (s : Equiv.Perm ι) ∈ Subgroup.zpowers r := s.2
    rw [← mem_powers_iff_mem_zpowers] at hs
    obtain ⟨k, hk⟩ := hs
    exact ⟨k, hk⟩
  obtain ⟨p, hp, hpinv, hclose⟩ :=
    group_uniform_universal (Γ := Subgroup.zpowers r) (Subgroup.zpowers r).subtype g
      (by
        intro s x
        obtain ⟨k, hk⟩ := hpow s
        show g (permAct (s : Equiv.Perm ι) x) = g x
        rw [← hk]
        exact hg k x)
      hK
      (by
        intro s x hx
        obtain ⟨k, hk⟩ := hpow s
        show permAct (s : Equiv.Perm ι) x ∈ K
        rw [← hk]
        exact hKsat k x hx)
      heps
  refine ⟨p, hp, ?_, hclose⟩
  intro k x
  exact hpinv ⟨r ^ k, Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), by simp⟩⟩ x


#print axioms solution
