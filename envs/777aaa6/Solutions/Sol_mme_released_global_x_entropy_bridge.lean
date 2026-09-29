-- Prove2me | solution 1 for mme_released_global_x_entropy_bridge
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T12:00:05.434534+00:00
-- url     : https://prove2.me/submissions/9443bc84-37a0-4e6d-8f8f-adbed225e74f

import Definitions.Def_mme_released_global_x_certificate
import Theorems.Thm_mme_released_global_x_data_valid
import Theorems.Thm_mme_entropy_penalty_of_positive_reference
import Theorems.Thm_mme_released_global_profile_normalization
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] jointRows alpha atom coarseCounts wordCounts shapeEquiv dualCounts

private theorem alpha_eq (o : Fin 6) (s : Fin 45) :
    (profile o).1 0 (shapeEquiv s) = (alphaQ o s : ℝ) := by
  unfold profile coarseCounts alphaQ
  simp only [Equiv.symm_apply_apply,Rat.cast_div,Rat.cast_natCast,Nat.cast_mul,Nat.cast_pow]
  norm_num [denominator]
  ring

private theorem marginal_sum (f : Shape → ℝ) (i : Fin 3) (j : Fin 9) :
    mme_modern_marginal (fun c ↦ c.val i) f j =
      ∑ c : Shape, if c.val i = j then f c else 0 := by
  unfold mme_modern_marginal
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) _).symm

private theorem marginal_eq (o : Fin 6) (i : Fin 3) (j : Fin 9) :
    mme_modern_marginal (fun c : Shape ↦ c.val i) ((profile o).1 0) j =
      (marginalQ o i j : ℝ) := by
  rw [marginal_sum,← Equiv.sum_comp shapeEquiv]
  simp only [marginalQ,Rat.cast_sum,apply_ite,Rat.cast_zero]
  apply Finset.sum_congr rfl
  intro s _
  have hs : (shapeEquiv s).val = shapeVector s := by
    simp only [shapeEquiv,Equiv.ofBijective_apply,shape]
  rw [hs,alpha_eq]

private theorem coordinate_moment (f : Shape → ℝ) (v : Fin 9 → ℝ) (i : Fin 3) :
    (∑ c, f c*v (c.val i)) =
      ∑ j, mme_modern_marginal (fun c : Shape ↦ c.val i) f j*v j := by
  rw [← Fintype.sum_fiberwise (fun c : Shape ↦ c.val i)]
  apply Finset.sum_congr rfl
  intro j _
  unfold mme_modern_marginal
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  rw [c.property]

theorem solution (o : Fin 6) :
    Real.log 2 * entropyPenalty ((profile o).1 0) ≤
      -(∑ s : Fin 45, (alphaQ o s : ℝ)*Real.log (dualQ o s : ℝ)) -
        entropy ((profile o).1 0) ∧
    (profile o).coarse 0 0 = ∑ j : Fin 9, Real.negMulLog (marginalQ o 0 j : ℝ) ∧
    entropy ((profile o).1 0) = ∑ s : Fin 45, Real.negMulLog (alphaQ o s : ℝ) := by
  classical
  have hv := mme_released_global_x_data_valid
  have hp := mme_released_global_profile_normalization o
  let q : Shape → ℝ := fun c ↦
    (∏ i : Fin 3, (dualCounts o i (c.val i) : ℝ))/(dualTotal o : ℝ)
  have hz : (0 : ℝ) < dualTotal o := by exact_mod_cast hv.2.2.2.2.1 o
  have hd (i : Fin 3) (j : Fin 9) : (0 : ℝ) < dualCounts o i j := by
    exact_mod_cast hv.2.2.2.1 o i j
  have he (s : Fin 45) : q (shapeEquiv s) = (dualQ o s : ℝ) := by
    dsimp [q,dualQ,dualMass]
    push_cast
    simp only [shapeEquiv,Equiv.ofBijective_apply,shape]
  have hq : ∀ c, 0 < q c := fun c ↦ div_pos (Finset.prod_pos (fun i _ ↦ hd i _)) hz
  have hqm : ∑ c, q c = 1 := by
    rw [← Equiv.sum_comp shapeEquiv]
    simp_rw [he]
    exact_mod_cast hv.2.2.2.2.2.1 o
  have hlog (c : Shape) : Real.log (q c) =
      (∑ i : Fin 3, Real.log (dualCounts o i (c.val i) : ℝ)) - Real.log (dualTotal o : ℝ) := by
    rw [show q c = (∏ i : Fin 3, (dualCounts o i (c.val i) : ℝ))/(dualTotal o : ℝ) from rfl,
      Real.log_div (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ (hd i _).ne')) hz.ne',
      Real.log_prod (fun i _ ↦ (hd i _).ne')]
  have moment (f : Shape → ℝ) : (∑ c, f c*Real.log (q c)) =
      (∑ i : Fin 3, ∑ j : Fin 9, mme_modern_marginal (fun c : Shape ↦ c.val i) f j *
        Real.log (dualCounts o i j : ℝ)) - (∑ c, f c)*Real.log (dualTotal o : ℝ) := by
    simp_rw [hlog,mul_sub,Finset.mul_sum]
    rw [Finset.sum_sub_distrib,Finset.sum_comm,← Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact coordinate_moment f (fun j ↦ Real.log (dualCounts o i j : ℝ)) i
  have hmom : ∀ rho ∈ SameMarginalDistributions ((profile o).1 0),
      (∑ c, rho c*Real.log (q c)) = ∑ c, (profile o).1 0 c*Real.log (q c) := by
    intro rho hr
    rw [moment,moment,hr.2.1,hp.2.1 0]
    simp_rw [hr.2.2]
  have hpen := mme_entropy_penalty_of_positive_reference ((profile o).1 0) q
    (hp.1 0) (hp.2.1 0) hq hqm hmom
  have hterm : (∑ c, (profile o).1 0 c*Real.log (q c)) =
      ∑ s : Fin 45, (alphaQ o s : ℝ)*Real.log (dualQ o s : ℝ) := by
    rw [← Equiv.sum_comp shapeEquiv]
    simp_rw [alpha_eq,he]
  refine ⟨by simpa only [hterm] using hpen,?_,?_⟩
  · unfold EntropyProfile.coarse massEntropy
    simp_rw [marginal_eq]
    have hm : (∑ j : Fin 9, (marginalQ o 0 j : ℝ)) = 1 := by
      exact_mod_cast hv.2.2.1 o 0
    rw [hm]
    simp [entropy]
  · unfold entropy
    rw [← Equiv.sum_comp shapeEquiv]
    simp_rw [alpha_eq]
