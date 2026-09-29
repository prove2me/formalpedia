-- Prove2me | solution 1 for PermutationDichotomy.equivariant_uniform_universal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:26:00.940005+00:00
-- url     : https://prove2.me/submissions/7dce4d7a-b3ab-4b07-a3c2-54b7b0b30da6

import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_PermutationDichotomy
import Theorems.Thm_PermutationDichotomy_attentionAlgebra_separatesPoints
import Theorems.Thm_PermutationDichotomy_symmetrize_error
import Theorems.Thm_PermutationDichotomy_equivariant_iff_exists_marked_invariant
set_option autoImplicit false
open scoped BigOperators
open PermutationDichotomy
namespace QuickEquivariant
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

theorem markAt_permAct (σ : Equiv.Perm ι) (i : ι) (x : Seq ι κ) :
    markAt i (permAct σ x) = permAct σ (markAt (σ i) x) := by
  funext j c
  cases c with
  | inl a => rfl
  | inr _ =>
      show (if j = i then (1 : ℝ) else 0) = if σ j = σ i then (1 : ℝ) else 0
      by_cases h : j = i
      · simp [h]
      · simp [h]

theorem marked_head_equivariant {G : Seq ι (κ ⊕ Unit) → ℝ} {σ : Equiv.Perm ι}
    (hG : ∀ z, G (permAct σ z) = G z) (i : ι) (x : Seq ι κ) :
    G (markAt i (permAct σ x)) = G (markAt (σ i) x) := by
  rw [markAt_permAct, hG]

theorem continuous_markAt (i : ι) : Continuous (markAt (κ := κ) i) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro c
  cases c with
  | inl a => exact (continuous_apply a).comp (continuous_apply j)
  | inr _ => exact continuous_const

theorem markAt_mem_markSaturation (act : Γ →* Equiv.Perm ι)
    {K : Set (Seq ι κ)} {x : Seq ι κ} (hx : x ∈ K) (i : ι) :
    markAt i x ∈ markSaturation act K := by
  refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr
    ⟨i, ⟨markAt i x, ⟨x, hx, rfl⟩, ?_⟩⟩⟩
  rw [MonoidHom.map_one]
  rfl

theorem isCompact_markSaturation (act : Γ →* Equiv.Perm ι)
    {K : Set (Seq ι κ)} (hK : IsCompact K) :
    IsCompact (markSaturation act K) :=
  isCompact_iUnion fun g =>
    isCompact_iUnion fun i =>
      ((hK.image (continuous_markAt i)).image (continuous_permAct (act g)))

theorem saturated_markSaturation (act : Γ →* Equiv.Perm ι) (K : Set (Seq ι κ)) :
    SaturatedUnder act (markSaturation act K) := by
  rintro tau z hz
  rw [markSaturation, Set.mem_iUnion] at hz ⊢
  obtain ⟨gamma, hz⟩ := hz
  rw [Set.mem_iUnion] at hz
  obtain ⟨i, w, hw, rfl⟩ := hz
  refine ⟨gamma * tau, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨i, w, hw, ?_⟩
  rw [MonoidHom.map_mul]
  exact (permAct_comp (act tau) (act gamma) w).symm

end QuickEquivariant
open QuickEquivariant

theorem solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    {Γ : Type*} [Group Γ] [Fintype Γ]
    (act : Γ →* Equiv.Perm ι) (F : Seq ι κ → Seq ι κ)
    (hFc : ∀ i a, Continuous fun x => F x i a) (hFe : EquivariantUnder act F)
    {K : Set (Seq ι κ)} (hK : IsCompact K) {eps : ℝ} (heps : 0 < eps) :
    ∃ P : κ → C(Seq ι (κ ⊕ Unit), ℝ),
      (∀ a, P a ∈ attentionAlgebra ι (κ ⊕ Unit)) ∧
      (∀ a, InvariantUnder act (fun z => P a z)) ∧
      (∀ (a : κ) (g : Γ) (i : ι) (x : Seq ι κ),
        P a (markAt i (permAct (act g) x)) = P a (markAt (act g i) x)) ∧
      (∀ x ∈ K, ∀ i a, |P a (markAt i x) - F x i a| < eps) := by
  obtain ⟨G, hGinv, hGF⟩ :=
    (equivariant_iff_exists_marked_invariant act F).mp ⟨hFc, hFe⟩
  have hstep : ∀ a : κ, ∃ p ∈ attentionAlgebra ι (κ ⊕ Unit),
      InvariantUnder act (fun z => p z) ∧
        ∀ z ∈ markSaturation act K, |p z - G a z| < eps := by
    intro a
    exact group_uniform_universal (ι := ι) (κ := κ ⊕ Unit) act (G a)
      (hGinv a) (isCompact_markSaturation act hK)
      (saturated_markSaturation act K) heps
  choose P hPmem hPinv hPclose using hstep
  refine ⟨P, hPmem, hPinv, ?_, ?_⟩
  · intro a g i x
    exact marked_head_equivariant (fun z => hPinv a g z) i x
  · intro x hx i a
    have h := hPclose a (markAt i x) (markAt_mem_markSaturation act hx i)
    rwa [← hGF x i a] at h

#print axioms solution
