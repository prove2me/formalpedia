-- Prove2me | solution 1 for MarkovEntanglement.separable_value_decomposition_with_shared_state
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-07T15:46:09.228004+00:00
-- url     : https://prove2.me/submissions/dff4f952-f9b0-48c2-bbab-b6ac8ce0808a

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

/-- A vector fixed by `γ P` with `P` stochastic and `γ < 1` is zero. -/
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
    {Z : Type*} [Fintype Z] [DecidableEq Z]
    (P : Matrix (JointZ S Z) (JointZ S Z) ℝ) (hP : IsTransitionMatrix P)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (Q : JointZ S Z → ℝ)
    (r : ∀ i, S i × Z → ℝ)
    (hQ : IsBellmanQ P (fun p => ∑ i, r i (p.1 i, p.2)) γ Q)
    (hsep : ∀ i, ∃ Pi : Matrix (S i × Z) (S i × Z) ℝ,
      ∀ p t, marginalZ i P p t = Pi (p.1 i, p.2) t) :
    ∃ Qi : ∀ i, S i × Z → ℝ, ∀ p : JointZ S Z, Q p = ∑ i, Qi i (p.1 i, p.2) := by
  classical
  choose Pl hPl using hsep
  let Phi : (∀ i, S i × Z → ℝ) →ₗ[ℝ] (JointZ S Z → ℝ) :=
    { toFun := fun h => fun p => ∑ i, h i (p.1 i, p.2)
      map_add' := by intro a b; funext p; simp [Finset.sum_add_distrib]
      map_smul' := by intro c a; funext p; simp [Finset.mul_sum] }
  let L : (JointZ S Z → ℝ) →ₗ[ℝ] (JointZ S Z → ℝ) := LinearMap.id - γ • P.mulVecLin
  have hLapply : ∀ (v : JointZ S Z → ℝ) (p : JointZ S Z),
      L v p = v p - γ * ∑ q, P p q * v q := by
    intro v p; simp [L, Matrix.mulVec, dotProduct]
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine eq_zero_of_eq_gamma_smul P hP γ hγ hγ1 v (fun p => ?_)
    have := congrFun hv p
    rw [hLapply] at this
    simp only [Pi.zero_apply] at this
    linarith
  -- marginalising: the joint transition acting on a function of one agent's
  -- coordinate and the shared state stays a function of those coordinates
  have hmarg : ∀ (i : Fin N) (g : S i × Z → ℝ) (p : JointZ S Z),
      ∑ q : JointZ S Z, P p q * g (q.1 i, q.2)
        = ∑ t : S i × Z, Pl i (p.1 i, p.2) t * g t := by
    intro i g p
    have hswap : ∑ t : S i × Z, marginalZ i P p t * g t
        = ∑ q : JointZ S Z, P p q * g (q.1 i, q.2) := by
      simp only [marginalZ, Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [Finset.sum_eq_single ((q.1 i, q.2) : S i × Z)]
      · simp
      · intro t _ ht
        refine if_neg ?_
        rintro ⟨h1, h2⟩
        exact ht (Prod.ext h1.symm h2.symm)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hswap]
    exact Finset.sum_congr rfl (fun t _ => by rw [hPl i p t])
  have hPD : ∀ h : ∀ i, S i × Z → ℝ, ∃ h' : ∀ i, S i × Z → ℝ,
      P.mulVecLin (Phi h) = Phi h' := by
    intro h
    refine ⟨fun i s => ∑ t : S i × Z, Pl i s t * h i t, ?_⟩
    funext p
    show ∑ q, P p q * (∑ i, h i (q.1 i, q.2))
      = ∑ i, ∑ t : S i × Z, Pl i (p.1 i, p.2) t * h i t
    calc ∑ q : JointZ S Z, P p q * (∑ i, h i (q.1 i, q.2))
        = ∑ i, ∑ q : JointZ S Z, P p q * h i (q.1 i, q.2) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun q _ => Finset.mul_sum _ _ _)
      _ = ∑ i, ∑ t : S i × Z, Pl i (p.1 i, p.2) t * h i t :=
          Finset.sum_congr rfl (fun i _ => hmarg i (h i) p)
  set D : Submodule ℝ (JointZ S Z → ℝ) := LinearMap.range Phi with hD
  have hLD : ∀ v ∈ D, L v ∈ D := by
    rintro v ⟨h, rfl⟩
    obtain ⟨h', hh'⟩ := hPD h
    refine ⟨h - γ • h', ?_⟩
    have : L (Phi h) = Phi h - γ • Phi h' := by simp [L, hh']
    rw [this, map_sub, map_smul]
  have hsurj : Function.Surjective (L.restrict hLD) := by
    rw [← LinearMap.injective_iff_surjective]
    intro a b hab
    apply Subtype.ext
    apply hLinj
    have := congrArg (fun w : D => (w : JointZ S Z → ℝ)) hab
    simpa [LinearMap.restrict_apply] using this
  obtain ⟨Q', hQ'⟩ := hsurj ⟨Phi r, ⟨r, rfl⟩⟩
  have hQ'eq : L (Q' : JointZ S Z → ℝ) = Phi r := congrArg Subtype.val hQ'
  have hQeq : L Q = Phi r := by
    funext p
    rw [hLapply]
    show Q p - γ * ∑ q, P p q * Q q = ∑ i, r i (p.1 i, p.2)
    linarith [hQ p]
  have hQQ' : Q = (Q' : JointZ S Z → ℝ) := hLinj (by rw [hQeq, hQ'eq])
  obtain ⟨h, hh⟩ := Q'.2
  exact ⟨h, fun p => by rw [hQQ', ← hh]; rfl⟩
