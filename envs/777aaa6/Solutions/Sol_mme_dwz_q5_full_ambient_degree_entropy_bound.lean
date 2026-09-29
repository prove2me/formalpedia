-- Prove2me | solution 1 for mme_dwz_q5_full_ambient_degree_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T13:58:38.773361+00:00
-- url     : https://prove2.me/submissions/58e577b3-8e54-4810-b0ab-3e0784f71214

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_dwz_fourth_global_entropy_upper
import Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZB2AmbientPublic.Fiber

theorem massEntropy_nat {C : Type*} [Fintype C] (n : C → ℕ) :
    massEntropy (fun c ↦ (n c : ℝ)) =
      ((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  simp only [massEntropy, entropy, Real.negMulLog, neg_mul,
    Finset.sum_neg_distrib, Nat.cast_sum]
  ring

theorem massEntropy_mul {C : Type*} [Fintype C] (x : C → ℝ) (m : ℝ) :
    massEntropy (fun c ↦ x c * m) = m * massEntropy x := by
  unfold massEntropy entropy
  rw [← Finset.sum_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem fiber_massEntropy {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g) :
    (∑ g, massEntropy (fun c : {c : C // grade c = g} ↦ (n c.val : ℝ))) =
      (∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  classical
  simp_rw [massEntropy_nat, hrow]
  rw [Finset.sum_sub_distrib,
    Fintype.sum_fiberwise grade (fun c ↦ (n c : ℝ) * Real.log (n c : ℝ))]

theorem fiber_factorial_entropy_bounds {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ) (S : ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g)
    (hS : ∀ g, M g ≤ S) :
    ((∏ g, (M g).factorial /
      ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) ≤
        Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * ((S : ℝ) + 1)) ^ Fintype.card C *
        ((∏ g, (M g).factorial /
          ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) := by
  classical
  have hc : (∑ g, Fintype.card {c : C // grade c = g}) = Fintype.card C := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      (Fintype.sum_fiberwise grade (fun _ ↦ (1 : ℕ)))
  have h := mme_regional_dependent_profile_entropy_bounds
    (fun g (c : {c : C // grade c = g}) ↦ n c.val) S
    (fun g ↦ (hrow g).trans_le (hS g))
  simpa only [fiber_massEntropy grade n M hrow, hc, hrow, Nat.cast_prod] using h


end MME.DWZB2AmbientPublic.Fiber

namespace MME.DWZB2AmbientPublic

open MME.DWZQ5ExactData MME.DWZFourthGlobalWitness

attribute [local irreducible] rawProfile rawCount rawDenominator component scale
  marginal coarseAddress alpha


theorem scale_pos : 0 < scale := mme_dwz_q5_exact_global_profile_certificate.1

theorem component_sum : (∑ c : Fin 45, component c) = scale :=
  mme_dwz_q5_exact_global_profile_certificate.2.2.1

theorem component_div_scale_eq_alpha (c : Fin 45) :
    (component c : ℚ) / scale = alpha c :=
  mme_dwz_q5_exact_global_profile_certificate.2.2.2.1 c

theorem component_marginal_count (i : Fin 3) (g : Fin 9) :
    (∑ c : Fin 45, if coarseAddress c i = g then component c else 0) = marginal i g :=
  mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.1 i g

theorem marginal_sum (i : Fin 3) : ∑ g : Fin 9, marginal i g = scale :=
  mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.1 i

theorem marginalXY_eq (g : Fin 9) : marginal 0 g = marginal 1 g :=
  mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.2.1 g

noncomputable def supportedLabelEquiv : Fin 45 ≃ MME.DWZQ5AsymptoticData.Cell :=
  Classical.choose mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.2.2.1

theorem supportedLabelEquiv_val (c : Fin 45) :
    (supportedLabelEquiv c).val = coarseAddress c :=
  Classical.choose_spec
    mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.2.2.1 c

theorem fourth_support_card : Fintype.card MME.DWZQ5AsymptoticData.Cell = 45 := by
  simpa only [Fintype.card_fin] using Fintype.card_congr supportedLabelEquiv.symm

theorem entropy_normalization {C : Type*} [Fintype C]
    (x : C → ℝ) (L : ℝ) (hL : L ≠ 0) (hsum : ∑ c, x c = L) :
    L * (∑ c, Real.negMulLog (x c / L)) =
      L * Real.log L - ∑ c, x c * Real.log (x c) := by
  have h : (∑ c, Real.negMulLog (x c)) =
      L * (∑ c, Real.negMulLog (x c / L)) + Real.negMulLog L := by
    calc
      _ = ∑ c, (L * Real.negMulLog (x c / L) +
          (x c / L) * Real.negMulLog L) := by
        apply Finset.sum_congr rfl
        intro c _
        simpa only [div_mul_cancel₀ _ hL] using Real.negMulLog_mul (x c / L) L
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
          ← Finset.sum_div, hsum, div_self hL, one_mul]
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at h
  simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

theorem component_fiber_sum (mode : Fin 3) (g : Fin 9) :
    (∑ c : {c : Fin 45 // coarseAddress c mode = g}, component c.val) =
      marginal mode g := by
  classical
  rw [← Finset.sum_subtype
    (Finset.univ.filter (fun c : Fin 45 ↦ coarseAddress c mode = g))
    (by intro c; simp) component, Finset.sum_filter]
  exact component_marginal_count mode g

theorem alpha_marginal_eq (mode : Fin 3) (g : Fin 9) :
    mme_modern_marginal (fun c ↦ coarseAddress c mode)
      (fun c ↦ (alpha c : ℝ)) g = (marginal mode g : ℝ) / scale := by
  classical
  have hc (c : Fin 45) : (alpha c : ℝ) = (component c : ℝ) / scale := by
    have hb := congrArg (fun q : ℚ ↦ (q : ℝ)) (component_div_scale_eq_alpha c).symm
    simpa only [Rat.cast_div, Rat.cast_natCast] using hb
  unfold mme_modern_marginal
  simp only [hc, ← Finset.sum_div, ← Nat.cast_sum, component_fiber_sum]

theorem feasible_count_sum (s : ℕ) (h : Fin 45 → ℕ)
    (hrow : ∀ (mode : Fin 3) (g : Fin 9),
      (∑ c : {c : Fin 45 // coarseAddress c mode = g}, h c.val) =
        marginal mode g * s) :
    ∑ c, h c = scale * s := by
  classical
  calc
    _ = ∑ g : Fin 9, ∑ c : {c : Fin 45 // coarseAddress c 0 = g}, h c.val :=
      (Fintype.sum_fiberwise (fun c : Fin 45 ↦ coarseAddress c 0) h).symm
    _ = ∑ g : Fin 9, marginal 0 g * s :=
      Finset.sum_congr rfl (fun g _ ↦ hrow 0 g)
    _ = _ := by rw [← Finset.sum_mul, marginal_sum]

theorem feasible_probability_marginal (s : ℕ) (hs : 0 < s) (h : Fin 45 → ℕ)
    (hrow : ∀ (mode : Fin 3) (g : Fin 9),
      (∑ c : {c : Fin 45 // coarseAddress c mode = g}, h c.val) =
        marginal mode g * s)
    (mode : Fin 3) (g : Fin 9) :
    mme_modern_marginal (fun c ↦ coarseAddress c mode)
        (fun c ↦ (h c : ℝ) / (scale * s : ℕ)) g =
      mme_modern_marginal (fun c ↦ coarseAddress c mode)
        (fun c ↦ (alpha c : ℝ)) g := by
  rw [alpha_marginal_eq]
  unfold mme_modern_marginal
  rw [← Finset.sum_div, ← Nat.cast_sum, hrow, Nat.cast_mul, Nat.cast_mul]
  have hscale : (scale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt scale_pos)
  have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  field_simp

theorem feasible_normalized_entropy_le (s : ℕ) (hs : 0 < s) (h : Fin 45 → ℕ)
    (hrow : ∀ (mode : Fin 3) (g : Fin 9),
      (∑ c : {c : Fin 45 // coarseAddress c mode = g}, h c.val) =
        marginal mode g * s) :
    (∑ c, Real.negMulLog ((h c : ℝ) / (scale * s : ℕ))) ≤
      (entropyUpper : ℝ) := by
  have hN : 0 < scale * s := Nat.mul_pos scale_pos hs
  apply mme_dwz_fourth_global_entropy_upper
  · intro c
    positivity
  · rw [← Finset.sum_div, ← Nat.cast_sum, feasible_count_sum s h hrow]
    exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  · exact feasible_probability_marginal s hs h hrow

theorem feasible_log_weight_le (s : ℕ) (hs : 0 < s) (h : Fin 45 → ℕ)
    (hrow : ∀ (mode : Fin 3) (g : Fin 9),
      (∑ c : {c : Fin 45 // coarseAddress c mode = g}, h c.val) =
        marginal mode g * s) (mode : Fin 3) :
    (∑ g : Fin 9, ((marginal mode g * s : ℕ) : ℝ) *
        Real.log ((marginal mode g * s : ℕ) : ℝ)) -
      ∑ c, (h c : ℝ) * Real.log (h c : ℝ) ≤
    ((scale * s : ℕ) : ℝ) * ((entropyUpper : ℝ) -
      ∑ g : Fin 9, Real.negMulLog ((marginal mode g : ℝ) / scale)) := by
  have hN : 0 < scale * s := Nat.mul_pos scale_pos hs
  have hN' : (((scale * s : ℕ) : ℝ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsumh : (∑ c : Fin 45, (h c : ℝ)) = ((scale * s : ℕ) : ℝ) := by
    exact_mod_cast feasible_count_sum s h hrow
  have hsumM : (∑ g : Fin 9, ((marginal mode g * s : ℕ) : ℝ)) =
      ((scale * s : ℕ) : ℝ) := by
    rw [← Nat.cast_sum, ← Finset.sum_mul, marginal_sum]
  have hh := entropy_normalization (fun c : Fin 45 ↦ (h c : ℝ)) _ hN' hsumh
  have hm := entropy_normalization
    (fun g : Fin 9 ↦ ((marginal mode g * s : ℕ) : ℝ)) _ hN' hsumM
  have hratio (g : Fin 9) :
      ((marginal mode g * s : ℕ) : ℝ) / ((scale * s : ℕ) : ℝ) =
        (marginal mode g : ℝ) / scale := by
    have hscale : (scale : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt scale_pos)
    have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
    simp only [Nat.cast_mul]
    field_simp
  simp only [hratio] at hm
  have hb := mul_le_mul_of_nonneg_left (feasible_normalized_entropy_le s hs h hrow)
    (Nat.cast_nonneg (scale * s) : (0 : ℝ) ≤ _)
  nlinarith

end MME.DWZB2AmbientPublic
namespace MME.DWZB2AmbientPublic

open MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open MME.DWZQ5AsymptoticData

attribute [local irreducible] rawProfile rawCount rawDenominator component scale
  marginal coarseAddress alpha D m n N M shape


theorem scalar_facts (t : ℕ) :
    0 < D ∧ N t = scale * (D * t) ∧
      ∀ (i : Fin 3) (g : Fin 9), M t i g.val = marginal i g * (D * t) := by
  classical
  have hD : 0 < D := by
    unfold D
    exact Finset.prod_pos (fun c _ ↦ (rawProfile c).denominator_pos)
  have hd (c : Fin 45) : (rawProfile c).denominator ∣ D := by
    unfold D
    exact Finset.dvd_prod_of_mem (fun c : Fin 45 ↦ (rawProfile c).denominator)
      (Finset.mem_univ c)
  have hn (c : Fin 45) : n t c = component c * (D * t) := by
    unfold n m
    exact Nat.mul_div_cancel'
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (hd c) t) (component c))
  refine ⟨hD, ?_, ?_⟩
  · unfold N
    simp only [hn, ← Finset.sum_mul, component_sum]
  · intro i g
    unfold M
    rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Fin 45 ↦ shape c i = g.val))
      (by intro c; simp) (n t), Finset.sum_filter]
    simp only [shape, Fin.val_inj]
    rw [← component_marginal_count i g, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp only [hn, zero_mul]

theorem admissible_table_log_weight_le (t : ℕ) (ht : 0 < t)
    (h : Cell → Fin (N t + 1)) (hh : h ∈ tables t) (mode : Fin 3) :
    (∑ g : Fin 9, (M t mode g.val : ℝ) * Real.log (M t mode g.val : ℝ)) -
      ∑ c : Cell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) ≤
    (N t : ℝ) * ((entropyUpper : ℝ) -
      ∑ g : Fin 9, Real.negMulLog ((marginal mode g : ℝ) / scale)) := by
  classical
  have hrowCell : ∀ (i : Fin 3) (g : Fin 9),
      (∑ c : {c : Cell // c.val i = g}, (h c.val).val) = M t i g.val := by
    simpa only [tables, Finset.mem_filter, Finset.mem_univ, true_and] using hh
  let hc : Fin 45 → ℕ := fun c ↦ (h (supportedLabelEquiv c)).val
  have hrow : ∀ (i : Fin 3) (g : Fin 9),
      (∑ c : {c : Fin 45 // coarseAddress c i = g}, hc c.val) =
        marginal i g * (D * t) := by
    intro i g
    let e : {c : Fin 45 // coarseAddress c i = g} ≃
        {c : Cell // c.val i = g} :=
      supportedLabelEquiv.subtypeEquiv (fun c ↦ by
        simp only [supportedLabelEquiv_val])
    calc
      _ = ∑ c : {c : Cell // c.val i = g}, (h c.val).val :=
        Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = M t i g.val := hrowCell i g
      _ = _ := (scalar_facts t).2.2 i g
  have hsum : (∑ c : Fin 45, (hc c : ℝ) * Real.log (hc c : ℝ)) =
      ∑ c : Cell, ((h c).val : ℝ) * Real.log ((h c).val : ℝ) :=
    Fintype.sum_equiv supportedLabelEquiv _ _ (fun _ ↦ rfl)
  have hb := feasible_log_weight_le (D * t) (Nat.mul_pos (scalar_facts t).1 ht) hc hrow mode
  simpa only [hsum, (scalar_facts t).2.2, (scalar_facts t).2.1] using hb

theorem degree_polynomial_entropy_bound (t : ℕ) (ht : 0 < t) (mode : Fin 3) :
    (degree t mode : ℝ) ≤ ((N t : ℝ) + 1) ^ 45 *
      Real.exp ((N t : ℝ) * ((entropyUpper : ℝ) -
        ∑ g : Fin 9, Real.negMulLog ((marginal mode g : ℝ) / scale))) := by
  classical
  let E := (N t : ℝ) * ((entropyUpper : ℝ) -
    ∑ g : Fin 9, Real.negMulLog ((marginal mode g : ℝ) / scale))
  have hweight (h : Cell → Fin (N t + 1)) (hh : h ∈ tables t) :
      ((∏ g : Fin 9, (M t mode g.val).factorial /
        ∏ c : {c : Cell // c.val mode = g}, ((h c.val).val).factorial : ℕ) : ℝ)
        ≤ Real.exp E := by
    have hrow : ∀ g : Fin 9,
        (∑ c : {c : Cell // c.val mode = g}, (h c.val).val) = M t mode g.val := by
      have ha : ∀ (i : Fin 3) (g : Fin 9),
          (∑ c : {c : Cell // c.val i = g}, (h c.val).val) = M t i g.val := by
        simpa only [tables, Finset.mem_filter, Finset.mem_univ, true_and] using hh
      exact ha mode
    have hS (g : Fin 9) : M t mode g.val ≤ ∑ g : Fin 9, M t mode g.val :=
      Finset.single_le_sum (f := fun g : Fin 9 ↦ M t mode g.val)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ g)
    have hb := (MME.DWZB2AmbientPublic.Fiber.fiber_factorial_entropy_bounds
      (C := Cell) (G := Fin 9) (fun c ↦ c.val mode)
      (fun c ↦ (h c).val) (fun g ↦ M t mode g.val)
      (∑ g : Fin 9, M t mode g.val) (by
        intro g
        convert hrow g using 1
        apply Finset.sum_congr
        · ext c
          simp only [Finset.mem_univ]
        · intro c _
          rfl) hS).1.trans
        (Real.exp_le_exp.mpr (admissible_table_log_weight_le t ht h hh mode))
    convert hb using 1
    congr 1
    apply Finset.prod_congr rfl
    intro g _
    congr 1
    apply Finset.prod_congr
    · ext c
      simp only [Finset.mem_univ]
    · intro c _
      rfl
  have hcard : (tables t).card ≤ (N t + 1) ^ 45 := by
    have hb := (tables t).card_le_univ
    simpa only [Fintype.card_fun, Fintype.card_fin,
      fourth_support_card] using hb
  unfold degree
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _h ∈ tables t, Real.exp E := Finset.sum_le_sum hweight
    _ = ((tables t).card : ℝ) * Real.exp E := by simp
    _ ≤ ((N t : ℝ) + 1) ^ 45 * Real.exp E := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos E).le
      exact_mod_cast hcard

theorem marginal_entropy_X_eq_Y :
    (∑ g : Fin 9, Real.negMulLog ((marginal 0 g : ℝ) / scale)) =
      ∑ g : Fin 9, Real.negMulLog ((marginal 1 g : ℝ) / scale) := by
  simp only [marginalXY_eq]

end MME.DWZB2AmbientPublic

open MME.DWZQ5AsymptoticData MME.DWZFourthGlobalWitness

theorem solution (t : ℕ) (ht : 0 < t) (mode : Fin 3) :
    (degree t mode : ℝ) ≤ ((N t : ℝ) + 1) ^ 45 *
      Real.exp ((N t : ℝ) * ((entropyUpper : ℝ) - marginalEntropy mode)) := by
  exact MME.DWZB2AmbientPublic.degree_polynomial_entropy_bound t ht mode
