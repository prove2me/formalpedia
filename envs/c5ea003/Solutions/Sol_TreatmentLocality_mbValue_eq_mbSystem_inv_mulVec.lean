-- Prove2me | solution 1 for TreatmentLocality.mbValue_eq_mbSystem_inv_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-22T00:36:46.650862+00:00
-- url     : https://prove2.me/submissions/7d91923b-5817-4723-8ed4-67df6b246c73

import Definitions.Def_TreatmentLocalityPlugIn
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped NNReal ENNReal

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The plug-in system matrix factors as `Diag(N^a) · (I - γ P̂^a)`. -/
lemma mbSystem_eq_diagonal_mul (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbSystem M v a
      = (Matrix.diagonal fun i => ∑ k, (v a).1 i k)
          * ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) := by
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Matrix.diagonal_apply_eq]
  have hentry : ((1 : Matrix S S ℝ) - M.γdisc • mbTrans v a) i j
      = (if i = j then (1 : ℝ) else 0) - M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k) := by
    simp [Matrix.sub_apply, Matrix.one_apply, mbTrans, smul_eq_mul]
  have hNi : (∑ k, (v a).1 i k) ≠ 0 := hN i
  have hc : (v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k) = (v a).1 i j := by
    field_simp
  have h2 : (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
      = M.γdisc * (v a).1 i j := by
    calc (∑ k, (v a).1 i k) * (M.γdisc * ((v a).1 i j / ∑ k, (v a).1 i k))
        = M.γdisc * ((v a).1 i j / (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)) := by ring
      _ = M.γdisc * (v a).1 i j := by rw [hc]
  rw [mbSystem_apply, hentry, mul_sub, h2]
  congr 1
  split_ifs <;> ring

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- With positive visit counts the plug-in value function solves the plug-in Bellman
system: `V̂^a = (Diag(N^a) - γ K^a)⁻¹ R^a`. -/
lemma mbValue_eq_solve_aux (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbValue M v a = (mbSystem M v a)⁻¹.mulVec (fun i => (v a).2 i) := by
  have hDinv : (Matrix.diagonal fun i => ∑ k, (v a).1 i k)⁻¹
      = Matrix.diagonal (fun i => (∑ k, (v a).1 i k)⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    rw [show (fun i => (∑ k, (v a).1 i k) * (∑ k, (v a).1 i k)⁻¹) = (fun _ : S => (1 : ℝ)) from
      funext fun i => mul_inv_cancel₀ (hN i)]
    exact Matrix.diagonal_one
  simp only [mbValue]
  rw [mbSystem_eq_diagonal_mul M v a hN, Matrix.mul_inv_rev, hDinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  simp [mbReward, div_eq_inv_mul]

/-- Applying the plug-in system matrix to a vector. -/
lemma mbSystem_mulVec_apply (M : Model S) (u : EstInput S) (a : Bool) (x : S → ℝ) (i : S) :
    (mbSystem M u a).mulVec x i = ∑ j, (u a).1 i j * (x i - M.γdisc * x j) := by
  simp only [Matrix.mulVec, dotProduct, mbSystem_apply, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  congr 1
  · have hstep : ∀ j : S, (if i = j then (∑ k, (u a).1 i k) else 0) * x j
        = (if i = j then (∑ k, (u a).1 i k) * x i else 0) := by
      intro j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl (fun j _ => hstep j), Finset.sum_ite_eq]
    simp [Finset.sum_mul]
  · exact Finset.sum_congr rfl fun j _ => by ring

/-- The plug-in system matrix as a continuous linear map of the statistics. -/
noncomputable def mbSystemL (M : Model S) (a : Bool) : EstInput S →L[ℝ] Matrix S S ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => mbSystem M u a
      map_add' := by
        intro u₁ u₂
        ext i j
        simp only [mbSystem_apply, Matrix.add_apply, Pi.add_apply, Prod.fst_add,
          Finset.sum_add_distrib]
        split_ifs <;> ring
      map_smul' := by
        intro r u
        ext i j
        simp only [mbSystem_apply, Matrix.smul_apply, Pi.smul_apply, Prod.smul_fst,
          smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
        split_ifs <;> ring }

lemma mbSystemL_apply (M : Model S) (a : Bool) (u : EstInput S) :
    mbSystemL M a u = mbSystem M u a := rfl

/-- The visit count as a continuous linear functional. -/
noncomputable def visitL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => ∑ k, (u a).1 i k
      map_add' := by intro u₁ u₂; simp [Finset.sum_add_distrib]
      map_smul' := by intro r u; simp [Finset.mul_sum] }

lemma visitL_apply (a : Bool) (i : S) (u : EstInput S) : visitL a i u = ∑ k, (u a).1 i k := rfl

/-- The reward statistic as a continuous linear functional. -/
noncomputable def rewardL (a : Bool) (i : S) : EstInput S →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (u a).2 i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

lemma rewardL_apply (a : Bool) (i : S) (u : EstInput S) : rewardL a i u = (u a).2 i := rfl

/-- Reading off a matrix entry, as a continuous linear functional. -/
noncomputable def entryL (i j : S) : Matrix S S ℝ →L[ℝ] ℝ :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap

lemma entryL_apply (i j : S) (A : Matrix S S ℝ) : entryL i j A = A i j := rfl

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

/-- The derivative of the inverse plug-in system matrix, as a continuous linear map. -/
noncomputable def invDL (M : Model S) (v : EstInput S) (a : Bool) :
    EstInput S →L[ℝ] Matrix S S ℝ :=
  (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))).comp (mbSystemL M a)

lemma invDL_apply (M : Model S) (v : EstInput S) (a : Bool) (h : EstInput S) :
    invDL M v a h = -(Ring.inverse (mbSystem M v a) * mbSystem M h a
      * Ring.inverse (mbSystem M v a)) := by
  show (-ContinuousLinearMap.mulLeftRight ℝ (Matrix S S ℝ)
    (Ring.inverse (mbSystem M v a)) (Ring.inverse (mbSystem M v a))) (mbSystemL M a h) = _
  rw [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, mbSystemL_apply]

/-- One summand of the gradient of the plug-in value function. -/
noncomputable def gradPiece (M : Model S) (v : EstInput S) (a : Bool) (s i : S) :
    EstInput S →L[ℝ] ℝ :=
  (Ring.inverse (mbSystem M v a) s i) • (rewardL a i)
    + ((v a).2 i) • ((entryL s i).comp (invDL M v a))

lemma gradPiece_apply (M : Model S) (v : EstInput S) (a : Bool) (s i : S) (h : EstInput S) :
    gradPiece M v a s i h
      = Ring.inverse (mbSystem M v a) s i * (h a).2 i
        - (v a).2 i * ((Ring.inverse (mbSystem M v a) * mbSystem M h a
            * Ring.inverse (mbSystem M v a)) s i) := by
  show (Ring.inverse (mbSystem M v a) s i) • (rewardL a i h)
    + ((v a).2 i) • ((entryL s i) (invDL M v a h)) = _
  rw [rewardL_apply, invDL_apply, entryL_apply, Matrix.neg_apply]
  simp only [smul_eq_mul]
  ring

/-- The plug-in value function is Fréchet differentiable in the statistics, with the
derivative obtained by differentiating the plug-in Bellman system. -/
theorem hasFDerivAt_mbValue (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) :
    HasFDerivAt (fun u : EstInput S => mbValue M u a s)
      (∑ i : S, gradPiece M v a s i) v := by
  have hsys : HasFDerivAt (fun u : EstInput S => mbSystem M u a) (mbSystemL M a) v :=
    (mbSystemL M a).hasFDerivAt
  have hDinvM : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a))
      (invDL M v a) v := by
    have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) hB.unit
    rw [hB.unit_spec] at h1
    have h2 : ((hB.unit⁻¹ : (Matrix S S ℝ)ˣ) : Matrix S S ℝ)
        = Ring.inverse (mbSystem M v a) := by
      rw [← Ring.inverse_unit hB.unit, hB.unit_spec]
    rw [h2] at h1
    exact h1.comp v hsys
  have hEach : ∀ i : S, HasFDerivAt
      (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (gradPiece M v a s i) v := by
    intro i
    have hc : HasFDerivAt (fun u : EstInput S => Ring.inverse (mbSystem M u a) s i)
        ((entryL s i).comp (invDL M v a)) v := (entryL s i).hasFDerivAt.comp v hDinvM
    have hd : HasFDerivAt (fun u : EstInput S => (u a).2 i) (rewardL a i) v :=
      (rewardL a i).hasFDerivAt
    exact hc.mul hd
  have hsum : HasFDerivAt
      (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i)
      (∑ i : S, gradPiece M v a s i) v :=
    HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hEach i)
  have hopen : ∀ᶠ u in nhds v, ∀ i : S, ∑ k, (u a).1 i k ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hne : visitL a i v ≠ 0 := by rw [visitL_apply]; exact hN i
    exact (visitL a i).continuous.continuousAt.eventually (eventually_ne_nhds hne)
  have heq : (fun u : EstInput S => mbValue M u a s)
      =ᶠ[nhds v] (fun u : EstInput S => ∑ i : S, Ring.inverse (mbSystem M u a) s i * (u a).2 i) := by
    filter_upwards [hopen] with u hu
    rw [mbValue_eq_solve_aux M u a hu, Matrix.nonsing_inv_eq_ringInverse]
    simp [Matrix.mulVec, dotProduct]
  exact hsum.congr_of_eventuallyEq heq

end TreatmentLocality

namespace TreatmentLocality

variable {S : Type*} [DecidableEq S] [Fintype S]

lemma sub_mbSystem_mulVec_mbValue (M : Model S) (v h : EstInput S) (a : Bool) :
    (fun i => (h a).2 i) - (mbSystem M h a).mulVec (mbValue M v a)
      = fun i => (h a).2 i + ∑ j, (h a).1 i j *
          (M.γdisc * mbValue M v a j - mbValue M v a i) := by
  funext i
  simp only [Pi.sub_apply, mbSystem_mulVec_apply]
  have hneg : ∀ j : S, (h a).1 i j * (M.γdisc * mbValue M v a j - mbValue M v a i)
      = -((h a).1 i j * (mbValue M v a i - M.γdisc * mbValue M v a j)) := fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => hneg j), sub_eq_add_neg]
  congr 1
  simp

/-- **The gradient of the model-based plug-in estimator**, in closed form. -/
theorem fderiv_mbValue_apply_aux (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) (hB : IsUnit (mbSystem M v a)) (s : S) (h : EstInput S) :
    fderiv ℝ (fun u : EstInput S => mbValue M u a s) v h
      = ((mbSystem M v a)⁻¹.mulVec (fun i =>
          (h a).2 i + ∑ j, (h a).1 i j *
            (M.γdisc * mbValue M v a j - mbValue M v a i))) s := by
  have key := hasFDerivAt_mbValue M v a hN hB s
  rw [key.fderiv, ContinuousLinearMap.sum_apply]
  have hri : Ring.inverse (mbSystem M v a) = (mbSystem M v a)⁻¹ :=
    (Matrix.nonsing_inv_eq_ringInverse _).symm
  simp only [gradPiece_apply, hri]
  set B := (mbSystem M v a)⁻¹ with hBdef
  set X := mbSystem M h a with hXdef
  rw [Finset.sum_sub_distrib]
  have e1 : ∑ i, B s i * (h a).2 i = (B.mulVec (fun i => (h a).2 i)) s := rfl
  have e2 : ∑ i, (v a).2 i * ((B * X * B) s i)
      = ((B * X * B).mulVec (fun i => (v a).2 i)) s := by
    show _ = ∑ i, (B * X * B) s i * (v a).2 i
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  have e3 : (B * X * B).mulVec (fun i => (v a).2 i)
      = B.mulVec (X.mulVec (mbValue M v a)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← mbValue_eq_solve_aux M v a hN]
  rw [e3, ← Pi.sub_apply, ← Matrix.mulVec_sub, sub_mbSystem_mulVec_mbValue M v h a]

end TreatmentLocality


open TreatmentLocality in
theorem solution {S : Type*} [DecidableEq S] [Fintype S]
    (M : Model S) (v : EstInput S) (a : Bool)
    (hN : ∀ i, ∑ k, (v a).1 i k ≠ 0) :
    mbValue M v a = (mbSystem M v a)⁻¹.mulVec (fun i => (v a).2 i) :=
  TreatmentLocality.mbValue_eq_solve_aux M v a hN
