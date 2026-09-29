-- Prove2me | solution 1 for BanditAlgorithm.mirror_descent_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T15:12:40.549398+00:00
-- url     : https://prove2.me/submissions/e4ec3075-1ac0-42ab-b6d9-1479306afc47

import Definitions.Def_OnlineLinearOptimization
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

open RealInnerProductSpace
open BanditAlgorithm

theorem solution
    {d : ℕ} {η : ℝ} (hη : 0 < η)
    {F : EuclideanSpace ℝ (Fin d) → ℝ} {D 𝒜 : Set (EuclideanSpace ℝ (Fin d))}
    (hF : IsLegendre F D) (h𝒜conv : Convex ℝ 𝒜) (h𝒜ne : 𝒜.Nonempty)
    (hmeet : (interior D ∩ 𝒜).Nonempty)
    (y a ã : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hiter : IsMirrorDescentIterates η F D 𝒜 y a ã) :
    ∀ a₀ ∈ 𝒜 ∩ D,
      (oloRegret a y n a₀ ≤
        (F a₀ - F (a 0)) / η +
          ∑ t ∈ Finset.range n,
            (⟪a t - a (t + 1), y t⟫ - (1 / η) * bregmanDiv F (a (t + 1)) (a t))) ∧
      (oloRegret a y n a₀ ≤
        (1 / η) * (F a₀ - F (a 0) +
          ∑ t ∈ Finset.range n, bregmanDiv F (a t) (ã (t + 1)))) := by
  intro a₀ ha₀
  let S : Set (EuclideanSpace ℝ (Fin d)) := 𝒜 ∩ D
  have hSconv : Convex ℝ S := h𝒜conv.inter hF.convexOn.1
  have hbreg_nonneg :
      ∀ {x z : EuclideanSpace ℝ (Fin d)}, x ∈ D → z ∈ interior D →
        0 ≤ bregmanDiv F x z := by
    intro x z hx hz
    let g : ℝ → EuclideanSpace ℝ (Fin d) := AffineMap.lineMap z x
    have hgconv : ConvexOn ℝ (g ⁻¹' D) (F ∘ g) := by
      exact hF.convexOn.comp_affineMap (AffineMap.lineMap z x)
    have hzero : (0 : ℝ) ∈ g ⁻¹' D := by
      simpa [g] using interior_subset hz
    have hone : (1 : ℝ) ∈ g ⁻¹' D := by
      simpa [g] using hx
    have hderiv :
        HasDerivAt (F ∘ g) ⟪gradient F z, x - z⟫ 0 := by
      have hFz :
          HasFDerivAt F
            ((InnerProductSpace.toDual ℝ _) (gradient F z)) (g 0) := by
        simpa [g] using
          (hF.differentiableAt z hz).hasGradientAt.hasFDerivAt
      simpa [g, real_inner_comm] using
        (hFz.comp_hasDerivAt (0 : ℝ) AffineMap.hasDerivAt_lineMap)
    have hslope :=
      hgconv.le_slope_of_hasDerivAt hzero hone (by norm_num) hderiv
    norm_num [slope, vsub_eq_sub] at hslope
    simp only [g, AffineMap.lineMap_apply_zero,
      AffineMap.lineMap_apply_one] at hslope
    dsimp [bregmanDiv]
    linarith
  have hstep_three (t : ℕ) :
      η * ⟪a (t + 1) - a₀, y t⟫ ≤
        bregmanDiv F a₀ (a t) -
          bregmanDiv F a₀ (a (t + 1)) -
            bregmanDiv F (a (t + 1)) (a t) := by
    have hlin :
        HasFDerivAt
          (fun b : EuclideanSpace ℝ (Fin d) => ⟪b, y t⟫)
          (innerSL ℝ (y t)) (a (t + 1)) := by
      simpa [real_inner_comm] using (innerSL ℝ (y t)).hasFDerivAt
    have hFnext :
        HasFDerivAt F
          ((InnerProductSpace.toDual ℝ _) (gradient F (a (t + 1))))
          (a (t + 1)) :=
      (hF.differentiableAt _ (hiter.mem_interior (t + 1))).hasGradientAt.hasFDerivAt
    have hgradlin :
        HasFDerivAt
          (fun b : EuclideanSpace ℝ (Fin d) =>
            ⟪gradient F (a t), b - a t⟫)
          (innerSL ℝ (gradient F (a t))) (a (t + 1)) := by
      convert ((innerSL ℝ (gradient F (a t))).hasFDerivAt.sub_const
        ⟪gradient F (a t), a t⟫) using 1
      · funext b
        simp [inner_sub_right]
    have hbreg_deriv :
        HasFDerivAt
          (fun b : EuclideanSpace ℝ (Fin d) => bregmanDiv F b (a t))
          ((InnerProductSpace.toDual ℝ _) (gradient F (a (t + 1))) -
            innerSL ℝ (gradient F (a t))) (a (t + 1)) := by
      simpa [bregmanDiv] using (hFnext.sub_const (F (a t))).sub hgradlin
    have hobj :
        HasFDerivAt
          (fun b : EuclideanSpace ℝ (Fin d) =>
            η * ⟪b, y t⟫ + bregmanDiv F b (a t))
          (η • innerSL ℝ (y t) +
            ((InnerProductSpace.toDual ℝ _) (gradient F (a (t + 1))) -
              innerSL ℝ (gradient F (a t)))) (a (t + 1)) := by
      simpa [smul_eq_mul] using (hlin.const_smul η).add hbreg_deriv
    have htangent :
        a₀ - a (t + 1) ∈ posTangentConeAt S (a (t + 1)) :=
      sub_mem_posTangentConeAt_of_segment_subset
        (hSconv.segment_subset (by simpa [S] using hiter.step_mem t) (by simpa [S] using ha₀))
    have hnonneg := (hiter.step_isMinOn t).localize.hasFDerivWithinAt_nonneg
      hobj.hasFDerivWithinAt htangent
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      InnerProductSpace.toDual_apply_apply, smul_eq_mul] at hnonneg
    dsimp [bregmanDiv]
    simp only [inner_sub_left, inner_sub_right] at hnonneg ⊢
    have hy₀ : ⟪y t, a₀⟫ = ⟪a₀, y t⟫ := by
      simpa using real_inner_comm a₀ (y t)
    have hynext : ⟪y t, a (t + 1)⟫ = ⟪a (t + 1), y t⟫ := by
      simpa using real_inner_comm (a (t + 1)) (y t)
    rw [hy₀, hynext] at hnonneg
    nlinarith
  have hinit_grad_nonneg :
      0 ≤ ⟪gradient F (a 0), a₀ - a 0⟫ := by
    have hFzero :
        HasFDerivAt F
          ((InnerProductSpace.toDual ℝ _) (gradient F (a 0))) (a 0) :=
      (hF.differentiableAt _ (hiter.mem_interior 0)).hasGradientAt.hasFDerivAt
    have htangent :
        a₀ - a 0 ∈ posTangentConeAt S (a 0) :=
      sub_mem_posTangentConeAt_of_segment_subset
        (hSconv.segment_subset (by simpa [S] using hiter.init_mem) (by simpa [S] using ha₀))
    have hnonneg := hiter.init_isMinOn.localize.hasFDerivWithinAt_nonneg
      hFzero.hasFDerivWithinAt htangent
    simpa only [InnerProductSpace.toDual_apply_apply] using hnonneg
  have hinit_breg_le :
      bregmanDiv F a₀ (a 0) ≤ F a₀ - F (a 0) := by
    dsimp [bregmanDiv]
    linarith
  have hsum_three :=
    Finset.sum_le_sum fun t (_ht : t ∈ Finset.range n) => hstep_three t
  have htel :
      (∑ t ∈ Finset.range n,
          (bregmanDiv F a₀ (a t) - bregmanDiv F a₀ (a (t + 1)))) =
        bregmanDiv F a₀ (a 0) - bregmanDiv F a₀ (a n) := by
    simpa using
      (Finset.sum_range_sub' (fun t => bregmanDiv F a₀ (a t)) n)
  have hsum_left :
      (∑ t ∈ Finset.range n, η * ⟪a (t + 1) - a₀, y t⟫) =
        η * ∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫ := by
    rw [Finset.mul_sum]
  have hsum_right :
      (∑ t ∈ Finset.range n,
          (bregmanDiv F a₀ (a t) -
            bregmanDiv F a₀ (a (t + 1)) -
              bregmanDiv F (a (t + 1)) (a t))) =
        bregmanDiv F a₀ (a 0) - bregmanDiv F a₀ (a n) -
          ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
    calc
      _ =
          (∑ t ∈ Finset.range n,
              (bregmanDiv F a₀ (a t) - bregmanDiv F a₀ (a (t + 1)))) -
            ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
              rw [Finset.sum_sub_distrib]
      _ = _ := by rw [htel]
  rw [hsum_left, hsum_right] at hsum_three
  have hterminal_nonneg :
      0 ≤ bregmanDiv F a₀ (a n) :=
    hbreg_nonneg ha₀.2 (hiter.mem_interior n)
  have hcore :
      η * (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) ≤
        F a₀ - F (a 0) -
          ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
    linarith
  have hscaled :
      (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) ≤
        (F a₀ - F (a 0)) / η -
          (1 / η) * ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
    rw [le_sub_iff_add_le, le_div_iff₀ hη]
    have hηne : η ≠ 0 := ne_of_gt hη
    calc
      ((∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
          (1 / η) * ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t)) * η =
          η * (∑ t ∈ Finset.range n, ⟪a (t + 1) - a₀, y t⟫) +
            ∑ t ∈ Finset.range n, bregmanDiv F (a (t + 1)) (a t) := by
              field_simp
      _ ≤ F a₀ - F (a 0) := by linarith
  have hfirst :
      oloRegret a y n a₀ ≤
        (F a₀ - F (a 0)) / η +
          ∑ t ∈ Finset.range n,
            (⟪a t - a (t + 1), y t⟫ -
              (1 / η) * bregmanDiv F (a (t + 1)) (a t)) := by
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
    rw [hreg_split, Finset.sum_sub_distrib, ← Finset.mul_sum]
    linarith
  have hstability (t : ℕ) :
      ⟪a t - a (t + 1), y t⟫ -
          (1 / η) * bregmanDiv F (a (t + 1)) (a t) ≤
        (1 / η) * bregmanDiv F (a t) (ã (t + 1)) := by
    have hidentity :
        η * ⟪a t - a (t + 1), y t⟫ =
          bregmanDiv F (a (t + 1)) (a t) +
            bregmanDiv F (a t) (ã (t + 1)) -
              bregmanDiv F (a (t + 1)) (ã (t + 1)) := by
      have hdual := hiter.dual_gradient_eq t
      dsimp [bregmanDiv]
      rw [hdual]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left]
      have hstar : starRingEnd ℝ η = η := by simp
      have hycur : ⟪y t, a t⟫ = ⟪a t, y t⟫ := by
        simpa using real_inner_comm (a t) (y t)
      have hynext :
          ⟪y t, a (t + 1)⟫ = ⟪a (t + 1), y t⟫ := by
        simpa using real_inner_comm (a (t + 1)) (y t)
      rw [hstar, hycur, hynext]
      ring
    have hproj_nonneg :
        0 ≤ bregmanDiv F (a (t + 1)) (ã (t + 1)) :=
      hbreg_nonneg (hiter.step_mem t).2 (hiter.dual_mem_interior t)
    have hηne : η ≠ 0 := ne_of_gt hη
    have hexact :
        ⟪a t - a (t + 1), y t⟫ -
            (1 / η) * bregmanDiv F (a (t + 1)) (a t) =
          (1 / η) *
            (bregmanDiv F (a t) (ã (t + 1)) -
              bregmanDiv F (a (t + 1)) (ã (t + 1))) := by
      field_simp
      linarith
    rw [hexact]
    have hinv_nonneg : 0 ≤ 1 / η := by positivity
    nlinarith
  have hsum_stability :=
    Finset.sum_le_sum fun t (_ht : t ∈ Finset.range n) => hstability t
  have hsum_stability' :
      (∑ t ∈ Finset.range n,
          (⟪a t - a (t + 1), y t⟫ -
            (1 / η) * bregmanDiv F (a (t + 1)) (a t))) ≤
        (1 / η) *
          ∑ t ∈ Finset.range n, bregmanDiv F (a t) (ã (t + 1)) := by
    calc
      _ ≤ ∑ t ∈ Finset.range n,
          (1 / η) * bregmanDiv F (a t) (ã (t + 1)) := hsum_stability
      _ = _ := by rw [Finset.mul_sum]
  have hsecond :
      oloRegret a y n a₀ ≤
        (1 / η) * (F a₀ - F (a 0) +
          ∑ t ∈ Finset.range n, bregmanDiv F (a t) (ã (t + 1))) := by
    calc
      oloRegret a y n a₀ ≤
          (F a₀ - F (a 0)) / η +
            ∑ t ∈ Finset.range n,
              (⟪a t - a (t + 1), y t⟫ -
                (1 / η) * bregmanDiv F (a (t + 1)) (a t)) := hfirst
      _ ≤ (F a₀ - F (a 0)) / η +
          (1 / η) *
            ∑ t ∈ Finset.range n, bregmanDiv F (a t) (ã (t + 1)) := by
              linarith
      _ = _ := by ring
  exact ⟨hfirst, hsecond⟩
