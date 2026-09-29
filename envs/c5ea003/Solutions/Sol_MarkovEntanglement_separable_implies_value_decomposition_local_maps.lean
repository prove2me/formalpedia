-- Prove2me | solution 1 for MarkovEntanglement.separable_implies_value_decomposition_local_maps
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T23:55:21.692766+00:00
-- url     : https://prove2.me/submissions/e1c5c12c-d520-415e-afed-f82ed12756aa

import Definitions.Def_markov_entanglement_multi
import Theorems.Thm_MarkovEntanglement_separable_apply_local_reward

open scoped BigOperators
open MarkovEntanglement

private theorem eq_zero_of_eq_gamma_smul {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ)
    (hP : IsTransitionMatrix P) (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (d : ι → ℝ)
    (hd : ∀ p, d p = γ * ∑ q, P p q * d q) : d = 0 := by
  classical
  funext p
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact (hι.false p).elim
  obtain ⟨p0, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) (fun p => |d p|)
      ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
  have hstep : |d p0| ≤ γ * |d p0| := by
    calc |d p0| = |γ * ∑ q, P p0 q * d q| := by rw [← hd p0]
      _ = γ * |∑ q, P p0 q * d q| := by rw [abs_mul, abs_of_nonneg hγ]
      _ ≤ γ * ∑ q, |P p0 q * d q| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hγ
      _ = γ * ∑ q, P p0 q * |d q| := by
          congr 1
          exact Finset.sum_congr rfl (fun q _ => by
            rw [abs_mul, abs_of_nonneg (hP.1 p0 q)])
      _ ≤ γ * ∑ q, P p0 q * |d p0| := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun q _ => ?_)) hγ
          exact mul_le_mul_of_nonneg_left (hmax q (Finset.mem_univ q)) (hP.1 p0 q)
      _ = γ * |d p0| := by rw [← Finset.sum_mul, hP.2 p0, one_mul]
  have h0 : |d p0| = 0 := by nlinarith [abs_nonneg (d p0)]
  have : |d p| ≤ 0 := by rw [← h0]; exact hmax p (Finset.mem_univ p)
  simpa using abs_nonpos_iff.mp this

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (P : Matrix (Joint S) (Joint S) ℝ) (hP : IsTransitionMatrix P) (hsep : IsSeparableN P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ Qmap : ∀ i, (S i → ℝ) → (S i → ℝ),
      ∀ (r : ∀ i, S i → ℝ) (Q : Joint S → ℝ),
        IsBellmanQ P (fun p => ∑ i, r i (p i)) γ Q →
          ∀ p : Joint S, Q p = ∑ i, Qmap i (r i) (p i) := by
  classical
  obtain ⟨Kn, x, Pj, hPj, hx, hPeq⟩ := hsep
  let L : (Joint S → ℝ) →ₗ[ℝ] (Joint S → ℝ) := LinearMap.id - γ • P.mulVecLin
  have hLapply : ∀ (v : Joint S → ℝ) (p : Joint S),
      L v p = v p - γ * ∑ q, P p q * v q := by
    intro v p; simp [L, Matrix.mulVec, dotProduct]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine eq_zero_of_eq_gamma_smul P hP γ hγ hγ1 v (fun p => ?_)
    have h := congrFun hv p
    rw [hLapply] at h
    simp only [Pi.zero_apply] at h
    linarith
  -- the subspace of functions of agent `i`'s coordinate alone
  let Phi : ∀ i : Fin N, (S i → ℝ) →ₗ[ℝ] (Joint S → ℝ) := fun i =>
    { toFun := fun g => fun p => g (p i)
      map_add' := by intro a b; funext p; simp
      map_smul' := by intro c a; funext p; simp }
  have hPD : ∀ (i : Fin N) (g : S i → ℝ),
      P.mulVecLin (Phi i g) = Phi i (fun s => ∑ k, x k * ∑ t : S i, Pj k i s t * g t) := by
    intro i g
    funext p
    show ∑ q, P p q * g (q i) = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * g t
    rw [show (fun q : Joint S => P p q * g (q i))
          = (fun q : Joint S => (∑ k, x k • tensorProdN (Pj k)) p q * g (q i)) from
        by rw [hPeq]]
    exact MarkovEntanglement.separable_apply_local_reward x Pj hPj hx i g p
  have hLD : ∀ i : Fin N, ∀ v ∈ LinearMap.range (Phi i), L v ∈ LinearMap.range (Phi i) := by
    rintro i v ⟨g, rfl⟩
    refine ⟨g - γ • (fun s => ∑ k, x k * ∑ t : S i, Pj k i s t * g t), ?_⟩
    have h : L (Phi i g)
        = Phi i g - γ • Phi i (fun s => ∑ k, x k * ∑ t : S i, Pj k i s t * g t) := by
      simp [L, hPD i g]
    rw [h, map_sub, map_smul]
  have hex : ∀ (i : Fin N) (ri : S i → ℝ), ∃ g : S i → ℝ, L (Phi i g) = Phi i ri := by
    intro i ri
    have hsurj : Function.Surjective (L.restrict (hLD i)) := by
      rw [← LinearMap.injective_iff_surjective]
      intro a b hab
      apply Subtype.ext
      apply hLinj
      have h := congrArg (fun w : LinearMap.range (Phi i) => (w : Joint S → ℝ)) hab
      simpa [LinearMap.restrict_apply] using h
    obtain ⟨w, hw⟩ := hsurj ⟨Phi i ri, ⟨ri, rfl⟩⟩
    obtain ⟨g, hg⟩ := w.2
    exact ⟨g, by rw [hg]; exact congrArg Subtype.val hw⟩
  choose Qmap hQmap using hex
  refine ⟨Qmap, ?_⟩
  intro r Q hQ
  have hQeq : L Q = ∑ i : Fin N, Phi i (r i) := by
    funext p
    rw [hLapply, Finset.sum_apply]
    show Q p - γ * ∑ q, P p q * Q q = ∑ i, r i (p i)
    linarith [hQ p]
  have hsum : L (∑ i : Fin N, Phi i (Qmap i (r i))) = ∑ i : Fin N, Phi i (r i) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hQmap i (r i))
  have hQQ : Q = ∑ i : Fin N, Phi i (Qmap i (r i)) := hLinj (by rw [hQeq, hsum])
  intro p
  rw [hQQ, Finset.sum_apply]
  rfl
