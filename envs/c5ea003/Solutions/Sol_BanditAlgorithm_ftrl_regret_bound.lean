-- Prove2me | solution 1 for BanditAlgorithm.ftrl_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T17:24:01.373685+00:00
-- url     : https://prove2.me/submissions/9b3f4f45-c2ec-4853-88fa-b973f523f2c3

import Definitions.Def_OnlineLinearOptimization
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic

open RealInnerProductSpace
open BanditAlgorithm

theorem solution
    {d : ℕ} {η : ℝ} (hη : 0 < η)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {D 𝒜 : Set (EuclideanSpace ℝ (Fin d))}
    (hF : ConvexOn ℝ D F) (h𝒜conv : Convex ℝ 𝒜) (h𝒜ne : 𝒜.Nonempty)
    (y a : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hiter : IsFTRLIterates η F D 𝒜 y a)
    (hdiff : ∀ t, DifferentiableAt ℝ F (a t)) :
    ∀ a₀ ∈ 𝒜 ∩ D,
      oloRegret a y n a₀ ≤
        (F a₀ - F (a 0)) / η +
          ∑ t ∈ Finset.range n,
            (⟪a t - a (t + 1), y t⟫ - (1 / η) * bregmanDiv F (a (t + 1)) (a t)) := by
  intro a₀ ha₀
  let S : Set (EuclideanSpace ℝ (Fin d)) := 𝒜 ∩ D
  let Φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun t b => η * ∑ s ∈ Finset.range t, ⟪b, y s⟫ + F b
  have hSconv : Convex ℝ S := h𝒜conv.inter hF.1
  have hmem : ∀ t, a t ∈ S := by
    intro t
    cases t with
    | zero => exact hiter.init_mem
    | succ t => simpa [Nat.succ_eq_add_one] using hiter.step_mem t
  have hmin : ∀ t, IsMinOn (Φ t) S (a t) := by
    intro t
    cases t with
    | zero =>
        simpa [Φ] using hiter.init_isMinOn
    | succ t =>
        simpa [Φ, Nat.succ_eq_add_one] using hiter.step_isMinOn t
  have hbreg (t : ℕ) :
      bregmanDiv F (a (t + 1)) (a t) ≤ Φ t (a (t + 1)) - Φ t (a t) := by
    have hlin :
        HasFDerivAt
          (∑ s ∈ Finset.range t,
            fun b : EuclideanSpace ℝ (Fin d) => ⟪b, y s⟫)
          (∑ s ∈ Finset.range t, innerSL ℝ (y s)) (a t) := by
      have hs : ∀ s ∈ Finset.range t,
          HasFDerivAt (fun b : EuclideanSpace ℝ (Fin d) => ⟪b, y s⟫)
            (innerSL ℝ (y s)) (a t) := by
        intro s hs
        simpa [real_inner_comm] using (innerSL ℝ (y s)).hasFDerivAt
      exact HasFDerivAt.sum hs
    have hΦ :
        HasFDerivAt (Φ t)
          (η • (∑ s ∈ Finset.range t, innerSL ℝ (y s)) +
            (InnerProductSpace.toDual ℝ _ ) (gradient F (a t))) (a t) := by
      convert (hlin.const_smul η).add ((hdiff t).hasGradientAt.hasFDerivAt) using 1
      funext b
      simp [Φ, smul_eq_mul]
    have htangent :
        a (t + 1) - a t ∈ posTangentConeAt S (a t) :=
      sub_mem_posTangentConeAt_of_segment_subset
        (hSconv.segment_subset (hmem t) (hmem (t + 1)))
    have hnonneg := (hmin t).localize.hasFDerivWithinAt_nonneg
      hΦ.hasFDerivWithinAt htangent
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at hnonneg
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply] at hnonneg
    simp only [innerSL_apply_apply, InnerProductSpace.toDual_apply_apply] at hnonneg
    have hsum :
        (∑ s ∈ Finset.range t, ⟪y s, a (t + 1) - a t⟫) =
          (∑ s ∈ Finset.range t, ⟪a (t + 1), y s⟫) -
            ∑ s ∈ Finset.range t, ⟪a t, y s⟫ := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      simp [real_inner_comm, inner_sub_right]
    rw [hsum] at hnonneg
    simp only [smul_eq_mul] at hnonneg
    dsimp [Φ, bregmanDiv]
    nlinarith
  have hstep (t : ℕ) :
      η * ⟪a (t + 1) - a₀, y t⟫ + bregmanDiv F (a (t + 1)) (a t) ≤
        Φ (t + 1) (a (t + 1)) - Φ t (a t) - η * ⟪a₀, y t⟫ := by
    have h := hbreg t
    simp only [Φ, Finset.sum_range_succ]
    simp only [inner_sub_left]
    nlinarith
  have hsum := Finset.sum_le_sum fun t (_ht : t ∈ Finset.range n) => hstep t
  have htel :
      (∑ t ∈ Finset.range n, (Φ (t + 1) (a (t + 1)) - Φ t (a t))) =
        Φ n (a n) - Φ 0 (a 0) := by
    let f : ℕ → ℝ := fun t => Φ t (a t)
    calc
      (∑ t ∈ Finset.range n, (Φ (t + 1) (a (t + 1)) - Φ t (a t))) =
          -(∑ t ∈ Finset.range n, (f t - f (t + 1))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro t ht
            dsimp [f]
            ring
      _ = -(f 0 - f n) := by rw [Finset.sum_range_sub']
      _ = Φ n (a n) - Φ 0 (a 0) := by
        dsimp [f]
        ring
  have hsum_left :
      (∑ t ∈ Finset.range n,
          (η * ⟪a (t + 1) - a₀, y t⟫ + bregmanDiv F (a (t + 1)) (a t))) =
        η * (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hsum_right :
      (∑ t ∈ Finset.range n,
          (Φ (t + 1) (a (t + 1)) - Φ t (a t) - η * ⟪a₀, y t⟫)) =
        (Φ n (a n) - Φ 0 (a 0)) -
          η * (∑ t ∈ Finset.range n, ⟪a₀, y t⟫) := by
    rw [Finset.sum_sub_distrib, htel, Finset.mul_sum]
  rw [hsum_left, hsum_right] at hsum
  have hfinal_min : Φ n (a n) ≤ Φ n a₀ := (hmin n) ha₀
  have hcore :
      η * (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) ≤
        F a₀ - F (a 0) := by
    have hΦzero : Φ 0 (a 0) = F (a 0) := by simp [Φ]
    have hΦcomp :
        Φ n a₀ - η * (∑ t ∈ Finset.range n, ⟪a₀, y t⟫) = F a₀ := by
      simp only [Φ]
      ring
    rw [hΦzero] at hsum
    calc
      _ ≤ Φ n (a n) - F (a 0) -
          η * (∑ t ∈ Finset.range n, ⟪a₀, y t⟫) := hsum
      _ ≤ Φ n a₀ - F (a 0) -
          η * (∑ t ∈ Finset.range n, ⟪a₀, y t⟫) := by linarith
      _ = F a₀ - F (a 0) := by rw [← hΦcomp]; ring
  have hηne : η ≠ 0 := ne_of_gt hη
  have hscaled :
      (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          (1 / η) * (∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t)) ≤
        (F a₀ - F (a 0)) / η := by
    rw [le_div_iff₀ hη]
    calc
      ((∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          (1 / η) * (∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t))) * η =
          η * (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
            ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
              field_simp
      _ ≤ F a₀ - F (a 0) := hcore
  dsimp [oloRegret]
  have hreg_split :
      (∑ t ∈ Finset.range n, ⟪a t - a₀, y t⟫) =
        (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          ∑ t ∈ Finset.range n, ⟪a t - a (t + 1), y t⟫ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [← inner_add_left]
    congr 1
    abel
  rw [hreg_split]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  nlinarith
