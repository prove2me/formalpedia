-- Prove2me | solution 1 for mme_dwz_q5_actual_Z_compatibility_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T14:04:58.00676+00:00
-- url     : https://prove2.me/submissions/2f877836-5ee9-4949-a2d3-f08a0992e066

import Theorems.Thm_mme_scaled_fiber_factorial_log_rate
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring
import Definitions.Def_mme_dwz_q5_global_asymptotic_data
import Theorems.Thm_mme_scaled_multinomial_log_rate
import Theorems.Thm_mme_dwz_q5_exact_global_profile_certificate
import Mathlib.Tactic
import Mathlib.Tactic.FinCases

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

noncomputable def compatibilityCount {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ) : ℕ :=
  (∏ i : Fin 9 × Fin 5, (fineMass coarse mu i).factorial /
    ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      (pooledMass shape coarse mu di.val).factorial) *
  (∏ d : Fin k ⊕ Fin 9, (∑ i, pooledMass shape coarse mu (d,i)).factorial /
    ∏ c : {c : Fin k // collapse shape coarse c = d}, (n c.val).factorial)

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

theorem pooled_balances {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (n : Fin k → ℕ) (hrows : ∀ c, ∑ l, mu 2 c l = n c) :
    (∀ i, (∑ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      pooledMass shape coarse mu di.val) = fineMass coarse mu i) ∧
    (∀ d, (∑ c : {c : Fin k // collapse shape coarse c = d}, n c.val) =
      ∑ i, pooledMass shape coarse mu (d,i)) := by
  classical
  constructor
  · rintro ⟨g,l⟩
    let e : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = (g,l)} ≃
        (Fin k ⊕ Fin 9) := {
      toFun := fun di ↦ di.val.1
      invFun := fun d ↦ ⟨(d,g,l),rfl⟩
      left_inv := by rintro ⟨⟨d,i⟩,h⟩; dsimp at h; subst i; rfl
      right_inv := fun _ ↦ rfl }
    calc
      _ = ∑ d, pooledMass shape coarse mu (d,g,l) := Fintype.sum_equiv e _ _
        (fun di ↦ by
          change pooledMass shape coarse mu (di.val.1,di.val.2) =
            pooledMass shape coarse mu (di.val.1,g,l)
          rw [di.property])
      _ = _ := by
        simp_rw [pooledMass_as_sum]
        rw [Finset.sum_comm, fineMass_ite]
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : coarse c = g
        · simp [hc]
        · simp [hc]
  · intro d
    rw [sum_subtype_ite]
    symm
    rw [Fintype.sum_prod_type]
    simp_rw [pooledMass_as_sum]
    calc
      _ = ∑ g : Fin 9, ∑ c, ∑ l : Fin 5,
          if collapse shape coarse c = d ∧ coarse c = g then mu 2 c l else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.sum_comm]
      _ = ∑ c, ∑ g : Fin 9, ∑ l : Fin 5,
          if collapse shape coarse c = d ∧ coarse c = g then mu 2 c l else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c _
        by_cases hc : collapse shape coarse c = d
        · simp [hc, hrows]
        · simp [hc]

end MME.DWZB2Compatibility

namespace MME.DWZB2Compatibility

theorem fineMass_scale {k : ℕ} (coarse : Fin k → Fin 9)
    (mu : Fin 3 → Fin k → Fin 5 → ℕ) (t : ℕ) (i : Fin 9 × Fin 5) :
    fineMass coarse (fun j c l ↦ mu j c l * t) i = fineMass coarse mu i * t := by
  simp only [fineMass, Finset.sum_mul]

theorem pooledMass_scale {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (t : ℕ) (di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5)) :
    pooledMass shape coarse (fun j c l ↦ mu j c l * t) di =
      pooledMass shape coarse mu di * t := by
  rcases di with ⟨d,g,l⟩
  cases d <;> simp only [pooledMass, fineMass_scale]
  all_goals split_ifs
  all_goals simp only [zero_mul, ← Finset.sum_mul, Nat.sub_mul]

theorem fiber_quotient_pos {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (a : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, a c.val = M g) (t : ℕ) :
    0 < ∏ g, (M g * t).factorial /
        ∏ c : {c : C // grade c = g}, (a c.val * t).factorial := by
  classical
  apply Finset.prod_pos
  intro g _
  have hm := Nat.multinomial_pos
    (s := Finset.univ) (f := fun c : {c : C // grade c = g} ↦ a c.val * t)
  simpa only [Nat.multinomial, ← Finset.sum_mul, hrow] using hm

noncomputable def rateNumerator {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ) (n : Fin k → ℕ) : ℝ :=
    (∑ i, (fineMass coarse mu i : ℝ) * Real.log (fineMass coarse mu i)) -
    (∑ di, (pooledMass shape coarse mu di : ℝ) * Real.log (pooledMass shape coarse mu di)) +
    (∑ d, ((∑ i, pooledMass shape coarse mu (d,i) : ℕ) : ℝ) *
      Real.log ((∑ i, pooledMass shape coarse mu (d,i) : ℕ) : ℝ)) -
    ∑ c, (n c : ℝ) * Real.log (n c)

theorem compatibility_scale_pos_and_rate {k : ℕ} (shape : Fin k → Fin 3 → ℕ)
    (coarse : Fin k → Fin 9) (mu : Fin 3 → Fin k → Fin 5 → ℕ)
    (n : Fin k → ℕ) (hrows : ∀ c, ∑ l, mu 2 c l = n c) :
    (∀ t, 0 < compatibilityCount shape coarse (fun j c l ↦ mu j c l * t)
      (fun c ↦ n c * t)) ∧
    Tendsto (fun t : ℕ ↦ Real.log
      (compatibilityCount shape coarse (fun j c l ↦ mu j c l * t)
        (fun c ↦ n c * t) : ℝ) / (t : ℝ)) atTop
      (𝓝 (rateNumerator shape coarse mu n)) := by
  classical
  have hb := pooled_balances shape coarse mu n hrows
  let Q₁ (t : ℕ) := ∏ i, (fineMass coarse mu i * t).factorial /
    ∏ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      (pooledMass shape coarse mu di.val * t).factorial
  let Q₂ (t : ℕ) := ∏ d, ((∑ i, pooledMass shape coarse mu (d,i)) * t).factorial /
    ∏ c : {c : Fin k // collapse shape coarse c = d}, (n c.val * t).factorial
  have hident (t : ℕ) : compatibilityCount shape coarse
      (fun j c l ↦ mu j c l * t) (fun c ↦ n c * t) = Q₁ t * Q₂ t := by
    simp only [compatibilityCount, fineMass_scale, pooledMass_scale, ← Finset.sum_mul]
    rfl
  have hb₁ : ∀ i, (∑ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      pooledMass shape coarse mu di.val) = fineMass coarse mu i := hb.1
  have hb₂ : ∀ d, (∑ c : {c : Fin k // collapse shape coarse c = d}, n c.val) =
      ∑ i, pooledMass shape coarse mu (d,i) := hb.2
  have hp₁ (t : ℕ) : 0 < Q₁ t := by
    apply Finset.prod_pos
    intro i _
    have hm := Nat.multinomial_pos (s := Finset.univ)
      (f := fun di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i} ↦
        pooledMass shape coarse mu di.val * t)
    simpa only [Nat.multinomial, ← Finset.sum_mul, hb₁] using hm
  have hp₂ (t : ℕ) : 0 < Q₂ t := by
    apply Finset.prod_pos
    intro d _
    have hm := Nat.multinomial_pos (s := Finset.univ)
      (f := fun c : {c : Fin k // collapse shape coarse c = d} ↦ n c.val * t)
    simpa only [Nat.multinomial, ← Finset.sum_mul, hb₂] using hm
  refine ⟨fun t ↦ by rw [hident]; exact Nat.mul_pos (hp₁ t) (hp₂ t), ?_⟩
  have h₁ : Tendsto (fun t : ℕ ↦ Real.log (Q₁ t : ℝ) / (t : ℝ)) atTop
      (𝓝 ((∑ i, (fineMass coarse mu i : ℝ) * Real.log (fineMass coarse mu i)) -
        ∑ di, (pooledMass shape coarse mu di : ℝ) * Real.log (pooledMass shape coarse mu di))) := by
    have h := mme_scaled_fiber_factorial_log_rate Prod.snd
      (pooledMass shape coarse mu) (fineMass coarse mu) (by
        intro i
        calc
          _ = ∑ di : {di : (Fin k ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
              pooledMass shape coarse mu di.val := by
            apply Finset.sum_congr
            · ext di
              simp
            · intro di _
              rfl
          _ = _ := hb₁ i)
    apply h.congr'
    filter_upwards [] with t
    symm
    apply congrArg (fun x : ℕ ↦ Real.log (x : ℝ) / (t : ℝ))
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (fun x : ℕ ↦ (fineMass coarse mu i * t).factorial / x)
    apply Finset.prod_congr
    · ext di
      simp
    · intro di _
      rfl
  have h₂ : Tendsto (fun t : ℕ ↦ Real.log (Q₂ t : ℝ) / (t : ℝ)) atTop
      (𝓝 ((∑ d, ((∑ i, pooledMass shape coarse mu (d,i) : ℕ) : ℝ) *
          Real.log ((∑ i, pooledMass shape coarse mu (d,i) : ℕ) : ℝ)) -
        ∑ c, (n c : ℝ) * Real.log (n c))) := by
    have h := mme_scaled_fiber_factorial_log_rate (collapse shape coarse) n
      (fun d ↦ ∑ i, pooledMass shape coarse mu (d,i)) (by
        intro d
        calc
          _ = ∑ c : {c : Fin k // collapse shape coarse c = d}, n c.val := by
            apply Finset.sum_congr
            · ext c
              simp
            · intro c _
              rfl
          _ = _ := hb₂ d)
    apply h.congr'
    filter_upwards [] with t
    symm
    apply congrArg (fun x : ℕ ↦ Real.log (x : ℝ) / (t : ℝ))
    apply Finset.prod_congr rfl
    intro d _
    apply congrArg (fun x : ℕ ↦ ((∑ i, pooledMass shape coarse mu (d,i)) * t).factorial / x)
    apply Finset.prod_congr
    · ext c
      simp
    · intro c _
      rfl
  have hlimit := h₁.add h₂
  convert hlimit using 1
  · funext t
    rw [hident, Nat.cast_mul,
      Real.log_mul (Nat.cast_ne_zero.mpr (hp₁ t).ne')
        (Nat.cast_ne_zero.mpr (hp₂ t).ne'), add_div]
  · unfold rateNumerator
    ring

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

theorem n_scale (t : ℕ) (c : Fin 45) : n t c = n 1 c * t := by
  rw [n_eq, n_eq, mul_one, mul_assoc]

theorem N_scale (t : ℕ) : N t = N 1 * t := by
  simp only [N, n_scale t, Finset.sum_mul]

theorem N_eq (t : ℕ) : N t = scale * (D * t) := by
  simp only [N, n_eq, ← Finset.sum_mul,
    mme_dwz_q5_exact_global_profile_certificate.2.2.1]

theorem N_one_pos : 0 < N 1 := by
  rw [N_eq, mul_one]
  exact Nat.mul_pos mme_dwz_q5_exact_global_profile_certificate.1 D_pos


end MME.DWZB2TargetRate

end ProofPart2

section ProofPart3

open BigOperators Filter MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Topology Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

namespace MME.DWZB2CompatibilityQ5

open MME.DWZQ5AsymptoticData MME.DWZB2TargetRate

attribute [local irreducible] MME.DWZQ5ExactData.rawProfile
  MME.DWZQ5ExactData.rawCount MME.DWZQ5ExactData.rawDenominator
  MME.DWZQ5ExactData.component MME.DWZQ5ExactData.scale
  MME.DWZQ5ExactData.marginal MME.DWZFourthGlobalWitness.coarseAddress

theorem m_scale (t : ℕ) (c : Fin 45) : m t c = m 1 c * t := by
  have hd : (rawProfile c).denominator ∣ component c * D :=
    dvd_mul_of_dvd_right
      (Finset.dvd_prod_of_mem (fun d : Fin 45 ↦ (rawProfile d).denominator)
        (Finset.mem_univ c)) (component c)
  simp only [m, mul_one, ← mul_assoc]
  rw [Nat.mul_comm (component c * D) t, Nat.mul_div_assoc t hd, Nat.mul_comm]

theorem mu_scale (t : ℕ) (i : Fin 3) (c : Fin 45) (l : Fin 5) :
    mu t i c l = mu 1 i c l * t := by
  fin_cases i <;> simp only [mu, z, m_scale t, mul_assoc, ite_mul, zero_mul]

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

theorem collapse_eq_generic (c : Fin 45) :
    collapse c = MME.DWZActualFineZCompatibility.collapse shape coarse c := by
  unfold collapse MME.DWZActualFineZCompatibility.collapse
    MME.DWZActualFineZCompatibility.boundary boundary
  split_ifs <;> rfl

theorem W_eq_compatibilityCount (t : ℕ) :
    W t = MME.DWZActualFineZCompatibility.compatibilityCount shape coarse (mu t) (n t) := by
  unfold W MME.DWZActualFineZCompatibility.compatibilityCount
  apply congrArg₂ Nat.mul
  · apply Finset.prod_congr rfl
    intro i _
    apply congrArg₂ Nat.div
    · exact congrArg Nat.factorial (F_eq_generic t i)
    · apply Finset.prod_congr
      · ext di
        simp
      · intro di _
        exact congrArg Nat.factorial (pooled_eq_generic t di.val)
  · apply Finset.prod_congr rfl
    intro d _
    apply congrArg₂ Nat.div
    · apply congrArg Nat.factorial
      apply Finset.sum_congr rfl
      intro i _
      exact pooled_eq_generic t (d,i)
    · let e : {c : Fin 45 // collapse c = d} ≃
          {c : Fin 45 // MME.DWZActualFineZCompatibility.collapse shape coarse c = d} :=
        Equiv.subtypeEquivRight (fun c ↦ by rw [collapse_eq_generic c])
      exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)

theorem compatibilityRate_eq :
    compatibilityRate = MME.DWZB2Compatibility.rateNumerator shape coarse (mu 1) (n 1) /
      (N 1 : ℝ) := by
  unfold compatibilityRate MME.DWZB2Compatibility.rateNumerator
  simp only [F_eq_generic, pooled_eq_generic, Nat.cast_sum]

theorem W_scaled (t : ℕ) : W t =
    MME.DWZActualFineZCompatibility.compatibilityCount shape coarse
      (fun i c l ↦ mu 1 i c l * t) (fun c ↦ n 1 c * t) := by
  rw [W_eq_compatibilityCount]
  have hmu : mu t = fun i c l ↦ mu 1 i c l * t := funext fun i ↦ funext fun c ↦
    funext fun l ↦ mu_scale t i c l
  have hn : n t = fun c ↦ n 1 c * t := funext fun c ↦ n_scale t c
  rw [hmu,hn]

theorem W_pos (t : ℕ) : 0 < W t := by
  have h := (MME.DWZB2Compatibility.compatibility_scale_pos_and_rate
    shape coarse (mu 1) (n 1) mu_sum).1 t
  rw [W_scaled]
  exact h

theorem W_log_rate :
    Tendsto (fun t : ℕ ↦ Real.log (W t : ℝ) / (N t : ℝ))
      atTop (𝓝 compatibilityRate) := by
  have h := (MME.DWZB2Compatibility.compatibility_scale_pos_and_rate
    shape coarse (mu 1) (n 1) mu_sum).2.div_const (N 1 : ℝ)
  rw [compatibilityRate_eq]
  apply h.congr'
  filter_upwards [] with t
  rw [W_scaled, N_scale t, Nat.cast_mul, div_div, mul_comm (t : ℝ) (N 1 : ℝ)]

theorem W_eventually_upper (a : ℝ) (ha : compatibilityRate < a) :
    ∀ᶠ t : ℕ in atTop, (W t : ℝ) ≤ Real.exp (a * (N t : ℝ)) := by
  have h := W_log_rate.eventually_lt_const ha
  filter_upwards [h, eventually_gt_atTop 0] with t ht ht0
  have hN : (0 : ℝ) < N t := by
    rw [N_scale, Nat.cast_mul]
    exact mul_pos (by exact_mod_cast N_one_pos) (by exact_mod_cast ht0)
  have hW : (0 : ℝ) < W t := by exact_mod_cast W_pos t
  exact (Real.log_le_iff_le_exp hW).mp ((div_lt_iff₀ hN).mp ht).le

theorem competitors_eventually_upper (a : ℝ) (ha : compatibilityRate < a) :
    ∀ᶠ t : ℕ in atTop, ((W t - 1 : ℕ) : ℝ) ≤ Real.exp (a * (N t : ℝ)) := by
  filter_upwards [W_eventually_upper a ha] with t ht
  exact le_trans (by exact_mod_cast Nat.sub_le (W t) 1) ht

end MME.DWZB2CompatibilityQ5

end ProofPart3

open Filter
open scoped Topology Classical
set_option warningAsError true

theorem solution :
    (∀ t : ℕ, 0 < MME.DWZQ5AsymptoticData.W t) ∧
    Filter.Tendsto (fun t : ℕ ↦ Real.log (MME.DWZQ5AsymptoticData.W t : ℝ) /
      (MME.DWZQ5AsymptoticData.N t : ℝ)) Filter.atTop
      (nhds MME.DWZQ5AsymptoticData.compatibilityRate) ∧
    (∀ a : ℝ, MME.DWZQ5AsymptoticData.compatibilityRate < a →
      ∀ᶠ t : ℕ in Filter.atTop, (MME.DWZQ5AsymptoticData.W t : ℝ) ≤
        Real.exp (a * (MME.DWZQ5AsymptoticData.N t : ℝ))) ∧
    (∀ a : ℝ, MME.DWZQ5AsymptoticData.compatibilityRate < a →
      ∀ᶠ t : ℕ in Filter.atTop, ((MME.DWZQ5AsymptoticData.W t - 1 : ℕ) : ℝ) ≤
        Real.exp (a * (MME.DWZQ5AsymptoticData.N t : ℝ))) := by
  exact ⟨MME.DWZB2CompatibilityQ5.W_pos, MME.DWZB2CompatibilityQ5.W_log_rate,
    MME.DWZB2CompatibilityQ5.W_eventually_upper,
    MME.DWZB2CompatibilityQ5.competitors_eventually_upper⟩
