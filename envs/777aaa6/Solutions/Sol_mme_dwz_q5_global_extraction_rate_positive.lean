-- Prove2me | solution 1 for mme_dwz_q5_global_extraction_rate_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T14:12:31.970195+00:00
-- url     : https://prove2.me/submissions/7c326b16-30fe-42e7-9fcd-da7f5128d0c9

import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Theorems.Thm_mme_dwz_q5_coarse_entropy_lower_bounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

section ProofPart1
open BigOperators Filter
open scoped Topology Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

namespace MME.DWZActualFineZCompatibility

def boundary {k : ℕ} (shape : Fin k → Fin 3 → ℕ) (c : Fin k) : Prop :=
  shape c 0 = 0 ∨ shape c 1 = 0

noncomputable def fineMass {k : ℕ} (coarse : Fin k → Fin 9)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (i : Fin 9 × Fin 5) : ℕ :=
  ∑ c : {c : Fin k // coarse c = i.1}, mu 2 c.val i.2

noncomputable def collapse {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (c : Fin k) : Fin k ⊕ Fin 9 :=
  if boundary shape c then Sum.inl c else Sum.inr (coarse c)

noncomputable def pooledMass {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) :
    (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
  | (Sum.inl c, (g,l)) => if boundary shape c ∧ coarse c = g then mu 2 c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then fineMass coarse mu (g,l) -
      ∑ c ∈ Finset.univ.filter (fun c ↦ boundary shape c ∧ coarse c = g), mu 2 c l
    else 0

end MME.DWZActualFineZCompatibility

open MME.DWZActualFineZCompatibility

namespace MME.DWZB2Compatibility

theorem sum_subtype_ite {C M : Type*} [Fintype C] [AddCommMonoid M]
    (P : C → Prop) [DecidablePred P] [Fintype {c : C // P c}] (f : C → M) :
    (∑ c : {c : C // P c}, f c.val) = ∑ c, if P c then f c else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (p := P) (F := inferInstance)
    (Finset.univ.filter P) (by simp) f).symm

theorem fineMass_ite {k : ℕ} (coarse : Fin k → Fin 9)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (g : Fin 9) (l : Fin 5) :
    fineMass coarse mu (g,l) = ∑ c, if coarse c = g then mu 2 c l else 0 := by
  exact sum_subtype_ite (fun c : Fin k ↦ coarse c = g) (fun c ↦ mu 2 c l)

theorem collapse_inl {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (c a : Fin k) :
    collapse shape coarse c = Sum.inl a ↔ c = a ∧ boundary shape a := by
  by_cases hb : boundary shape c
  · simp only [collapse, if_pos hb, Sum.inl.injEq]
    exact ⟨fun h ↦ ⟨h, h ▸ hb⟩, And.left⟩
  · simp only [collapse, if_neg hb, Sum.inr_ne_inl, false_iff, not_and]
    intro h
    exact h ▸ hb

theorem collapse_inr {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (c : Fin k) (g : Fin 9) :
    collapse shape coarse c = Sum.inr g ↔ ¬boundary shape c ∧ coarse c = g := by
  by_cases hb : boundary shape c <;> simp [collapse, hb]

theorem pooledMass_as_sum {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (d : Fin k ⊕ Fin 9) (g : Fin 9) (l : Fin 5) :
    pooledMass shape coarse mu (d,g,l) =
      ∑ c, if collapse shape coarse c = d ∧ coarse c = g then mu 2 c l else 0 := by
  classical
  cases d with
  | inl a =>
    simp only [pooledMass, collapse_inl]
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hca
      simp [hca]
    · simp
  | inr g' =>
    simp only [pooledMass, collapse_inr]
    by_cases hgg : g' = g
    · subst g'
      rw [if_pos rfl]
      have hpart :
          (∑ c, if boundary shape c ∧ coarse c = g then mu 2 c l else 0) +
          (∑ c, if (¬boundary shape c ∧ coarse c = g) ∧ coarse c = g then mu 2 c l else 0) =
          fineMass coarse mu (g,l) := by
        rw [← Finset.sum_add_distrib, fineMass_ite]
        apply Finset.sum_congr rfl
        intro c _
        by_cases hb : boundary shape c <;> by_cases hc : coarse c = g <;> simp [hb,hc]
      rw [Finset.sum_filter]
      omega
    · rw [if_neg hgg]
      symm
      apply Finset.sum_eq_zero
      intro c _
      split_ifs with hc
      · exact False.elim (hgg (hc.1.2.symm.trans hc.2))
      · rfl

end MME.DWZB2Compatibility

end ProofPart1

section ProofPart2
open BigOperators Filter MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open scoped Topology Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace MME.DWZB2TargetRate

theorem D_pos : 0 < D := Finset.prod_pos (fun c _ ↦ (rawProfile c).denominator_pos)

theorem n_eq (t : ℕ) (c : Fin 45) : n t c = component c * (D * t) := by
  apply Nat.mul_div_cancel'
  have hc : (rawProfile c).denominator ∣ D :=
    Finset.dvd_prod_of_mem (fun d : Fin 45 ↦ (rawProfile d).denominator) (Finset.mem_univ c)
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hc t) (component c)

theorem N_eq (t : ℕ) : N t = scale * (D * t) := by
  simp only [N, n_eq, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]

theorem N_one_pos : 0 < N 1 := by
  rw [N_eq, mul_one]
  exact Nat.mul_pos mme_dwz_q5_exact_global_profile_certificate.1 D_pos

end MME.DWZB2TargetRate

end ProofPart2

section ProofPart3
open BigOperators MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
namespace MME.DWZB2CompatibilityQ5
open MME.DWZQ5AsymptoticData MME.DWZB2TargetRate

attribute [local irreducible] MME.DWZQ5ExactData.rawProfile
  MME.DWZQ5ExactData.rawCount MME.DWZQ5ExactData.rawDenominator
  MME.DWZQ5ExactData.component MME.DWZQ5ExactData.scale
  MME.DWZQ5ExactData.marginal MME.DWZFourthGlobalWitness.coarseAddress

theorem mu_sum (c : Fin 45) : ∑ l, mu 1 2 c l = n 1 c := by
  simp only [mu, z, ← Finset.sum_mul, (rawProfile c).count_sum]
  rfl

theorem F_eq_generic (t : ℕ) (i : Fin 9 × Fin 5) :
    F t i = MME.DWZActualFineZCompatibility.fineMass coarse (mu t) i := by
  unfold F MME.DWZActualFineZCompatibility.fineMass
  apply Finset.sum_congr
  · ext c
    simp
  · intro c _
    rfl

theorem pooled_eq_generic (t : ℕ) (di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5)) :
    pooled t di = MME.DWZActualFineZCompatibility.pooledMass shape coarse (mu t) di := by
  rcases di with ⟨d,g,l⟩
  cases d <;> simp only [pooled, MME.DWZActualFineZCompatibility.pooledMass,
    boundary, MME.DWZActualFineZCompatibility.boundary]
  all_goals split_ifs
  all_goals try rfl

end MME.DWZB2CompatibilityQ5

end ProofPart3

section ProofPart4
open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace MME.DWZB2Positivity

/-- Homogeneous entropy subadditivity for any finite nonnegative table,
including zero rows, zero columns, and a zero total. -/
theorem table_entropy_subadditivity
    {D L : Type*} [Fintype D] [Fintype L]
    (x : D → L → ℝ) (hx : ∀ d l, 0 ≤ x d l) :
    (∑ l, (∑ d, x d l) * Real.log (∑ d, x d l)) -
      (∑ d, ∑ l, x d l * Real.log (x d l)) +
      (∑ d, (∑ l, x d l) * Real.log (∑ l, x d l)) ≤
      (∑ d, ∑ l, x d l) * Real.log (∑ d, ∑ l, x d l) := by
  let row (d : D) : ℝ := ∑ l, x d l
  let col (l : L) : ℝ := ∑ d, x d l
  let total : ℝ := ∑ d, row d
  have hr (d : D) : 0 ≤ row d := Finset.sum_nonneg (fun l _ ↦ hx d l)
  have hc (l : L) : 0 ≤ col l := Finset.sum_nonneg (fun d _ ↦ hx d l)
  have ht : 0 ≤ total := Finset.sum_nonneg (fun d _ ↦ hr d)
  have hxrow (d : D) (l : L) : x d l ≤ row d :=
    Finset.single_le_sum (fun l _ ↦ hx d l) (Finset.mem_univ l)
  have hxcol (d : D) (l : L) : x d l ≤ col l :=
    Finset.single_le_sum (fun d _ ↦ hx d l) (Finset.mem_univ d)
  have hrowtotal (d : D) : row d ≤ total :=
    Finset.single_le_sum (fun d _ ↦ hr d) (Finset.mem_univ d)
  have hcolsum : ∑ l, col l = total := by
    dsimp [col, total, row]
    exact Finset.sum_comm
  by_cases ht0 : total = 0
  · have hx0 (d : D) (l : L) : x d l = 0 := by
      have h := (hxrow d l).trans (hrowtotal d)
      rw [ht0] at h
      exact le_antisymm h (hx d l)
    simp only [hx0, Finset.sum_const_zero, Real.log_zero, zero_mul,
      sub_self, add_zero, le_refl]
  have htpos : 0 < total := lt_of_le_of_ne ht (Ne.symm ht0)
  have hterm (d : D) (l : L) :
      x d l * Real.log (row d) + x d l * Real.log (col l) -
        x d l * Real.log (x d l) - x d l * Real.log total ≤
      row d * col l / total - x d l := by
    by_cases hzero : x d l = 0
    · simpa only [hzero, zero_mul, add_zero, sub_zero] using
        div_nonneg (mul_nonneg (hr d) (hc l)) ht
    have hpos : 0 < x d l := lt_of_le_of_ne (hx d l) (Ne.symm hzero)
    have hrpos : 0 < row d := hpos.trans_le (hxrow d l)
    have hcpos : 0 < col l := hpos.trans_le (hxcol d l)
    have hypos : 0 < row d * col l / total :=
      div_pos (mul_pos hrpos hcpos) htpos
    calc
      _ = x d l * Real.log ((row d * col l / total) / x d l) := by
        rw [Real.log_div hypos.ne' hpos.ne',
          Real.log_div (mul_pos hrpos hcpos).ne' htpos.ne',
          Real.log_mul hrpos.ne' hcpos.ne']
        ring
      _ ≤ x d l * (((row d * col l / total) / x d l) - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.log_le_sub_one_of_pos (div_pos hypos hpos)) (hx d l)
      _ = row d * col l / total - x d l := by
        field_simp
  have hsum := Finset.sum_le_sum (fun d (_ : d ∈ Finset.univ) ↦
    Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) ↦ hterm d l))
  have hrow : (∑ d, ∑ l, x d l * Real.log (row d)) =
      ∑ d, row d * Real.log (row d) := by
    simp only [← Finset.sum_mul, row]
  have hcol : (∑ d, ∑ l, x d l * Real.log (col l)) =
      ∑ l, col l * Real.log (col l) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, col]
  have htotal : (∑ d, ∑ l, x d l * Real.log total) =
      total * Real.log total := by
    simp only [← Finset.sum_mul, total, row]
  have hprod : (∑ d, ∑ l, row d * col l / total) = total := by
    simp only [← Finset.sum_div, ← Finset.mul_sum, hcolsum]
    rw [← Finset.sum_mul]
    change total * total / total = total
    exact mul_div_cancel_right₀ total ht0
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [hrow, hcol, htotal, hprod] at hsum
  change _ ≤ _ - total at hsum
  change (∑ l, col l * Real.log (col l)) -
    (∑ d, ∑ l, x d l * Real.log (x d l)) +
    (∑ d, row d * Real.log (row d)) ≤ total * Real.log total
  linarith

end MME.DWZB2Positivity
end ProofPart4

section ProofPart5
open BigOperators Filter MME.DWZQ5ExactData MME.DWZQ5AsymptoticData
open MME.DWZB2TargetRate MME.DWZB2CompatibilityQ5
open scoped Classical Topology
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace MME.DWZB2CompatibilityPositivity

attribute [local irreducible] MME.DWZQ5ExactData.rawProfile
  MME.DWZQ5ExactData.rawCount MME.DWZQ5ExactData.rawDenominator
  MME.DWZQ5ExactData.component MME.DWZQ5ExactData.scale
  MME.DWZQ5ExactData.marginal MME.DWZFourthGlobalWitness.coarseAddress

def poolGrade : Fin 45 ⊕ Fin 9 → Fin 9 := Sum.elim coarse id

theorem pool_off_grade (t : ℕ) (d : Fin 45 ⊕ Fin 9) (g : Fin 9) (l : Fin 5)
    (h : poolGrade d ≠ g) : pooled t (d,g,l) = 0 := by
  cases d with
  | inl c => simp only [poolGrade, Sum.elim_inl] at h; simp [pooled,h]
  | inr g' => simp only [poolGrade, Sum.elim_inr, id_eq] at h; simp [pooled,h]

theorem pool_column (t : ℕ) (g : Fin 9) (l : Fin 5) :
    ∑ d : Fin 45 ⊕ Fin 9, pooled t (d,g,l) = F t (g,l) := by
  simp_rw [pooled_eq_generic, MME.DWZB2Compatibility.pooledMass_as_sum]
  rw [Finset.sum_comm, F_eq_generic, MME.DWZB2Compatibility.fineMass_ite]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : coarse c = g
  · simp [hc]
  · simp [hc]

theorem fine_total (g : Fin 9) :
    ∑ l : Fin 5, F 1 (g,l) = M 1 2 g.val := by
  simp_rw [F_eq_generic, MME.DWZB2Compatibility.fineMass_ite]
  rw [Finset.sum_comm]
  unfold M
  rw [MME.DWZB2Compatibility.sum_subtype_ite]
  apply Finset.sum_congr rfl
  intro c _
  have he : coarse c = g ↔ shape c 2 = g.val := Fin.ext_iff
  by_cases hc : coarse c = g
  · simp [hc, he.mp hc, mu_sum]
  · simp [hc, mt he.mpr hc]

theorem pool_row (t : ℕ) (d : Fin 45 ⊕ Fin 9) :
    ∑ i : Fin 9 × Fin 5, pooled t (d,i) =
      ∑ l : Fin 5, pooled t (d,poolGrade d,l) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_single (poolGrade d)
  · intro g _ hg
    apply Finset.sum_eq_zero
    intro l _
    exact pool_off_grade t d g l (Ne.symm hg)
  · simp

theorem M_seed (g : Fin 9) : M 1 2 g.val = marginal 2 g * D := by
  unfold M
  rw [MME.DWZB2Compatibility.sum_subtype_ite]
  simp_rw [n_eq, mul_one]
  have h (c : Fin 45) :
      (if shape c 2 = g.val then component c * D else 0) =
      (if MME.DWZFourthGlobalWitness.coarseAddress c 2 = g then component c else 0) * D := by
    by_cases hc : MME.DWZFourthGlobalWitness.coarseAddress c 2 = g
    · simp [shape,hc]
    · have hv : (MME.DWZFourthGlobalWitness.coarseAddress c 2).val ≠ g.val :=
        fun he ↦ hc (Fin.ext he)
      simp [shape,hc,hv]
  simp_rw [h]
  rw [← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.1]

theorem M_total : ∑ g : Fin 9, M 1 2 g.val = N 1 := by
  simp only [M_seed, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.2.2.2.2.2.1, N_eq, mul_one]

theorem M_normalized (g : Fin 9) :
    (M 1 2 g.val : ℝ) / (N 1 : ℝ) = (marginal 2 g : ℝ) / scale := by
  rw [M_seed, N_eq, mul_one, Nat.cast_mul, Nat.cast_mul]
  have hd : (D : ℝ) ≠ 0 := by exact_mod_cast D_pos.ne'
  field_simp

theorem normalized_entropy_nonneg {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (s : ℝ) (hs : 0 < s)
    (hsum : ∑ i, a i = s) :
    (s * Real.log s - ∑ i, a i * Real.log (a i)) / s =
      ∑ i, Real.negMulLog (a i / s) := by
  have hterm (i : ι) : Real.negMulLog (a i / s) =
      (a i * Real.log s - a i * Real.log (a i)) / s := by
    by_cases hi : a i = 0
    · simp [hi, Real.negMulLog]
    · rw [Real.negMulLog, Real.log_div hi hs.ne']
      ring
  simp only [hterm, ← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hsum]

theorem marginalEntropy_mass : marginalEntropy 2 =
    ((N 1 : ℝ) * Real.log (N 1 : ℝ) -
      ∑ g : Fin 9, (M 1 2 g.val : ℝ) * Real.log (M 1 2 g.val : ℝ)) / (N 1 : ℝ) := by
  have he := normalized_entropy_nonneg (fun g : Fin 9 ↦ (M 1 2 g.val : ℝ))
    (N 1 : ℝ) (by exact_mod_cast N_one_pos)
    (by rw [← Nat.cast_sum, M_total])
  rw [he]
  simp only [M_normalized, marginalEntropy]

theorem pooled_row_entropy_sum :
    (∑ g : Fin 9, ∑ d : Fin 45 ⊕ Fin 9,
      ((∑ l : Fin 5, pooled 1 (d,g,l) : ℕ) : ℝ) *
        Real.log ((∑ l : Fin 5, pooled 1 (d,g,l) : ℕ) : ℝ)) =
    ∑ d : Fin 45 ⊕ Fin 9,
      (∑ i : Fin 9 × Fin 5, pooled 1 (d,i) : ℝ) *
        Real.log (∑ i : Fin 9 × Fin 5, pooled 1 (d,i) : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_eq_single (poolGrade d)]
  · simp only [← Nat.cast_sum, pool_row]
  · intro g _ hg
    have hz : ∑ l : Fin 5, pooled 1 (d,g,l) = 0 :=
      Finset.sum_eq_zero (fun l _ ↦ pool_off_grade 1 d g l (Ne.symm hg))
    rw [hz]
    simp
  · simp

theorem pooled_cell_entropy_sum :
    (∑ g : Fin 9, ∑ d : Fin 45 ⊕ Fin 9, ∑ l : Fin 5,
      (pooled 1 (d,g,l) : ℝ) * Real.log (pooled 1 (d,g,l) : ℝ)) =
    ∑ di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5),
      (pooled 1 di : ℝ) * Real.log (pooled 1 di : ℝ) := by
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_prod_type]

theorem pooled_total (g : Fin 9) :
    (∑ d : Fin 45 ⊕ Fin 9, ∑ l : Fin 5, pooled 1 (d,g,l)) = M 1 2 g.val := by
  rw [Finset.sum_comm]
  simp only [pool_column, fine_total]

theorem compatibility_bound_of_table_bound
    (htable : ∀ g : Fin 9,
      (∑ l : Fin 5, (F 1 (g,l) : ℝ) * Real.log (F 1 (g,l) : ℝ)) -
      (∑ d : Fin 45 ⊕ Fin 9, ∑ l : Fin 5,
        (pooled 1 (d,g,l) : ℝ) * Real.log (pooled 1 (d,g,l) : ℝ)) +
      (∑ d : Fin 45 ⊕ Fin 9, (∑ l : Fin 5, pooled 1 (d,g,l) : ℝ) *
        Real.log (∑ l : Fin 5, pooled 1 (d,g,l) : ℝ)) ≤
      (M 1 2 g.val : ℝ) * Real.log (M 1 2 g.val : ℝ)) :
    compatibilityRate ≤ targetRate - marginalEntropy 2 := by
  have hsum := Finset.sum_le_sum (fun g (_ : g ∈ Finset.univ) ↦ htable g)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [pooled_cell_entropy_sum] at hsum
  have hrow := pooled_row_entropy_sum
  simp only [Nat.cast_sum] at hrow
  rw [hrow] at hsum
  have hF : (∑ g : Fin 9, ∑ l : Fin 5,
      (F 1 (g,l) : ℝ) * Real.log (F 1 (g,l) : ℝ)) =
      ∑ i : Fin 9 × Fin 5, (F 1 i : ℝ) * Real.log (F 1 i : ℝ) :=
    (Fintype.sum_prod_type (fun i : Fin 9 × Fin 5 ↦
      (F 1 i : ℝ) * Real.log (F 1 i : ℝ))).symm
  rw [hF] at hsum
  have hnpos : (0 : ℝ) ≤ N 1 := Nat.cast_nonneg _
  have hd := div_le_div_of_nonneg_right
    (sub_le_sub_right hsum (∑ c : Fin 45, (n 1 c : ℝ) * Real.log (n 1 c : ℝ))) hnpos
  unfold compatibilityRate targetRate
  rw [marginalEntropy_mass]
  convert hd using 1
  ring

theorem compatibilityRate_le_targetRate_sub_Z_entropy :
    compatibilityRate ≤ targetRate - marginalEntropy 2 := by
  apply compatibility_bound_of_table_bound
  intro g
  have h := MME.DWZB2Positivity.table_entropy_subadditivity
    (fun (d : Fin 45 ⊕ Fin 9) (l : Fin 5) ↦ (pooled 1 (d,g,l) : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _)
  simpa only [← Nat.cast_sum, pool_column, pooled_total] using h

end MME.DWZB2CompatibilityPositivity
end ProofPart5

section ProofPart6
open MME.DWZQ5AsymptoticData
namespace MME.DWZB2Positivity
theorem extractionRate_positive_of_compatibility_bound
    (hW : compatibilityRate ≤ targetRate - marginalEntropy 2) :
    (1 / 100 : ℝ) < extractionRate := by
  have hU : (DWZFourthGlobalWitness.entropyUpper : ℝ) < 71 / 25 := by
    norm_num [DWZFourthGlobalWitness.entropyUpper]
  have hT := mme_dwz_q5_coarse_entropy_lower_bounds.1
  have hX := mme_dwz_q5_coarse_entropy_lower_bounds.2 0
  have hY := mme_dwz_q5_coarse_entropy_lower_bounds.2 1
  have hZ := mme_dwz_q5_coarse_entropy_lower_bounds.2 2
  unfold extractionRate hashRate
  have h0 : 0 < targetRate - 1 / 100 := by linarith
  have hx : (DWZFourthGlobalWitness.entropyUpper : ℝ) - marginalEntropy 0 <
      targetRate - 1 / 100 := by linarith
  have hy : (DWZFourthGlobalWitness.entropyUpper : ℝ) - marginalEntropy 1 <
      targetRate - 1 / 100 := by linarith
  have hw : compatibilityRate < targetRate - 1 / 100 := by linarith
  have hh := max_lt h0 (max_lt hx (max_lt hy hw))
  linarith

end MME.DWZB2Positivity
end ProofPart6

theorem solution :
    MME.DWZQ5AsymptoticData.compatibilityRate ≤
      MME.DWZQ5AsymptoticData.targetRate - MME.DWZQ5AsymptoticData.marginalEntropy 2 ∧
    (1 / 100 : ℝ) < MME.DWZQ5AsymptoticData.extractionRate := by
  have hW := MME.DWZB2CompatibilityPositivity.compatibilityRate_le_targetRate_sub_Z_entropy
  exact ⟨hW, MME.DWZB2Positivity.extractionRate_positive_of_compatibility_bound hW⟩

