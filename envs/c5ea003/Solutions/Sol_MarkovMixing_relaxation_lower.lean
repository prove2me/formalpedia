-- Prove2me | solution 1 for MarkovMixing.relaxation_lower
-- status  : ACCEPTED   (prove)
-- author  : @chenmin
-- created : 2026-08-22T16:22:59.915465+00:00
-- url     : https://prove2.me/submissions/76a9b6a0-1123-410a-a526-1a3b8f84129d

import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_convergence_theorem
import Mathlib.Tactic

set_option maxHeartbeats 1000000

open scoped BigOperators
open MarkovMixing

namespace RelaxLower

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma le_tvDist (μ ν : V → ℝ) (A : Finset V) :
    |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν := by
  have hb : BddAbove (Set.range fun B : Finset V => |∑ x ∈ B, μ x - ∑ x ∈ B, ν x|) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb A

lemma le_distStationary (P : Matrix V V ℝ) (π : V → ℝ) (t : ℕ) (x : V) :
    tvDist (rowDist P t x) π ≤ distStationary P π t := by
  have hb : BddAbove (Set.range fun y : V => tvDist (rowDist P t y) π) :=
    Set.Finite.bddAbove (Set.finite_range _)
  exact le_ciSup hb x

/-- The `ℓ¹` distance is at most twice the total variation distance. -/
lemma l1_le_two_tvDist (μ ν : V → ℝ) : ∑ y, |μ y - ν y| ≤ 2 * tvDist μ ν := by
  classical
  set A : Finset V := Finset.univ.filter fun y => ν y ≤ μ y with hA
  have hsplit : ∑ y, |μ y - ν y|
      = (∑ y ∈ A, (μ y - ν y)) + ∑ y ∈ Aᶜ, (ν y - μ y) := by
    rw [← Finset.sum_add_sum_compl A (fun y => |μ y - ν y|)]
    congr 1
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [hA, Finset.mem_filter] at hy
      exact abs_of_nonneg (by linarith [hy.2])
    · refine Finset.sum_congr rfl fun y hy => ?_
      rw [Finset.mem_compl, hA, Finset.mem_filter] at hy
      have : ¬ (ν y ≤ μ y) := fun h => hy ⟨Finset.mem_univ y, h⟩
      rw [abs_of_nonpos (by linarith [not_le.mp this])]
      ring
  have h1 : ∑ y ∈ A, (μ y - ν y) ≤ tvDist μ ν := by
    calc ∑ y ∈ A, (μ y - ν y) = ∑ y ∈ A, μ y - ∑ y ∈ A, ν y := Finset.sum_sub_distrib _ _
      _ ≤ |∑ y ∈ A, μ y - ∑ y ∈ A, ν y| := le_abs_self _
      _ ≤ tvDist μ ν := le_tvDist μ ν A
  have h2 : ∑ y ∈ Aᶜ, (ν y - μ y) ≤ tvDist μ ν := by
    calc ∑ y ∈ Aᶜ, (ν y - μ y) = -(∑ y ∈ Aᶜ, μ y - ∑ y ∈ Aᶜ, ν y) := by
          rw [← Finset.sum_sub_distrib]
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ ≤ |∑ y ∈ Aᶜ, μ y - ∑ y ∈ Aᶜ, ν y| := neg_le_abs _
      _ ≤ tvDist μ ν := le_tvDist μ ν Aᶜ
  rw [hsplit]
  linarith

lemma root_bound {r c : ℝ} {m : ℕ} (hm : m ≠ 0) (hc : 0 < c) (hr : 0 ≤ r) (h : r ^ m ≤ c) :
    r ≤ c ^ ((m : ℝ)⁻¹) := by
  have hb : (c ^ ((m : ℝ)⁻¹)) ^ m = c := by
    rw [← Real.rpow_natCast (c ^ ((m : ℝ)⁻¹)) m, ← Real.rpow_mul hc.le,
      inv_mul_cancel₀ (by exact_mod_cast hm), Real.rpow_one]
  exact le_of_pow_le_pow_left₀ hm (Real.rpow_nonneg hc.le _) (by rw [hb]; exact h)

/-- If `f` is an eigenfunction with eigenvalue `lam ≠ 1`, then `|lam|^t ≤ 2 d(t)`. -/
lemma abs_pow_le (P : Matrix V V ℝ) (π : V → ℝ) (hπ : IsStationary P π)
    {lam : ℝ} (h : IsEigenvalue P lam) (hne : lam ≠ 1) (t : ℕ) :
    |lam| ^ t ≤ 2 * distStationary P π t := by
  classical
  obtain ⟨f, hf0, hf⟩ := h
  obtain ⟨x1, hx1⟩ := Function.ne_iff.mp hf0
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) (fun y => |f y|) ⟨x1, Finset.mem_univ x1⟩
  have hm : 0 < |f x0| := lt_of_lt_of_le (abs_pos.mpr hx1) (hx0 x1 (Finset.mem_univ x1))
  have hcol : ∀ z, ∑ y, π y * P y z = π z := fun z => congrFun hπ.2 z
  have hperp : ∑ y, π y * f y = 0 := by
    have h2 : ∑ y, π y * (P.mulVec f) y = ∑ z, π z * f z := by
      have e : ∀ y : V, π y * (P.mulVec f) y = ∑ z, (π y * P y z) * f z := by
        intro y
        show π y * (∑ z, P y z * f z) = _
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← Finset.sum_mul, hcol z]
    rw [hf] at h2
    have h3 : ∑ y, π y * (lam • f) y = lam * ∑ y, π y * f y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by simp [Pi.smul_apply]; ring
    rw [h3] at h2
    have h4 : (lam - 1) * (∑ y, π y * f y) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with hh | hh
    · exact absurd (by linarith : lam = 1) hne
    · exact hh
  have hpow : ∀ s : ℕ, (P ^ s).mulVec f = (lam ^ s) • f := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hf, Matrix.mulVec_smul, ih, smul_smul, pow_succ]
      rw [mul_comm (lam ^ s) lam]
  have key : |lam| ^ t * |f x0| ≤ 2 * distStationary P π t * |f x0| := by
    have e0 : |lam ^ t * f x0| = |lam| ^ t * |f x0| := by rw [abs_mul, abs_pow]
    have e2 : ∑ y, (P ^ t) x0 y * f y = lam ^ t * f x0 := by
      have := congrFun (hpow t) x0
      simpa [Matrix.mulVec, dotProduct] using this
    have e1 : lam ^ t * f x0 = ∑ y, ((P ^ t) x0 y - π y) * f y := by
      rw [← e2]
      have e : ∀ y : V, ((P ^ t) x0 y - π y) * f y = (P ^ t) x0 y * f y - π y * f y :=
        fun y => by ring
      rw [Finset.sum_congr rfl (fun y _ => e y), Finset.sum_sub_distrib, hperp, sub_zero]
    calc |lam| ^ t * |f x0| = |∑ y, ((P ^ t) x0 y - π y) * f y| := by rw [← e0, e1]
      _ ≤ ∑ y, |((P ^ t) x0 y - π y) * f y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |(P ^ t) x0 y - π y| * |f x0| := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hx0 y (Finset.mem_univ y)) (abs_nonneg _)
      _ = (∑ y, |(P ^ t) x0 y - π y|) * |f x0| := (Finset.sum_mul _ _ _).symm
      _ ≤ (2 * tvDist (rowDist P t x0) π) * |f x0| :=
          mul_le_mul_of_nonneg_right (l1_le_two_tvDist _ _) (abs_nonneg _)
      _ ≤ 2 * distStationary P π t * |f x0| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          linarith [le_distStationary P π t x0]
  exact le_of_mul_le_mul_right key hm

end RelaxLower

open RelaxLower

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : MarkovMixing.IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (hap : MarkovMixing.Aperiodic P) (π : V → ℝ) (hπ : MarkovMixing.IsStationary P π)
    (hrev : MarkovMixing.DetailedBalance P π) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (MarkovMixing.relaxationTime P - 1) * Real.log (1 / (2 * ε)) ≤
      (MarkovMixing.mixingTime P π ε : ℝ) := by
  classical
  obtain ⟨α, ⟨hα0, hα1⟩, C, hC, hCd⟩ := MarkovMixing.convergence_theorem P hP hirr hap π hπ
  have hsmall : ∀ δ : ℝ, 0 < δ → ∃ t : ℕ, distStationary P π t ≤ δ := by
    intro δ hδ
    obtain ⟨t, ht⟩ := exists_pow_lt_of_lt_one (div_pos hδ hC) hα1
    refine ⟨t, ?_⟩
    have h2 : C * α ^ t < δ := by
      calc C * α ^ t < C * (δ / C) := mul_lt_mul_of_pos_left ht hC
        _ = δ := by field_simp
    linarith [hCd t]
  set T : ℕ := MarkovMixing.mixingTime P π ε with hT_def
  have hTmem : distStationary P π T ≤ ε := Nat.sInf_mem (hsmall ε hε)
  have hTnn : (0:ℝ) ≤ (T:ℝ) := Nat.cast_nonneg T
  by_cases hSne : ({r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|}).Nonempty
  · obtain ⟨t1, ht1⟩ := hsmall (1/4) (by norm_num)
    have ht1ne : t1 ≠ 0 := by
      intro h
      obtain ⟨r, l, hl, hlne, rfl⟩ := hSne
      have hz := abs_pow_le P π hπ hl hlne 0
      rw [h] at ht1
      simp at hz
      linarith
    have hUB : ∀ r ∈ {r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|},
        r ≤ (2 * (1/4:ℝ)) ^ ((t1:ℝ)⁻¹) := by
      rintro r ⟨l, hl, hlne, rfl⟩
      refine root_bound ht1ne (by norm_num) (abs_nonneg l) ?_
      calc |l| ^ t1 ≤ 2 * distStationary P π t1 := abs_pow_le P π hπ hl hlne t1
        _ ≤ 2 * (1/4) := by linarith
    have ht1pos : (0:ℝ) < (t1:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ht1ne
    have hbdd : BddAbove {r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} := ⟨_, hUB⟩
    have hq_lt : MarkovMixing.lambdaStar P < 1 := by
      have h1 : MarkovMixing.lambdaStar P ≤ (2 * (1/4:ℝ)) ^ ((t1:ℝ)⁻¹) := csSup_le hSne hUB
      have h2 : (2 * (1/4:ℝ)) ^ ((t1:ℝ)⁻¹) < 1 :=
        Real.rpow_lt_one (by norm_num) (by norm_num) (inv_pos.mpr ht1pos)
      linarith
    have hq_nonneg : 0 ≤ MarkovMixing.lambdaStar P := by
      obtain ⟨r, hr⟩ := hSne
      have h1 : r ≤ MarkovMixing.lambdaStar P := le_csSup hbdd hr
      obtain ⟨l, -, -, rfl⟩ := hr
      linarith [abs_nonneg l]
    have hrel : MarkovMixing.relaxationTime P - 1
        = MarkovMixing.lambdaStar P / (1 - MarkovMixing.lambdaStar P) := by
      show (1 - MarkovMixing.lambdaStar P)⁻¹ - 1 = _
      have hne0 : (1 : ℝ) - MarkovMixing.lambdaStar P ≠ 0 := by linarith
      field_simp
      ring
    rcases le_or_gt (1/2 : ℝ) ε with hc | hc
    · have hK : Real.log (1 / (2*ε)) ≤ 0 := by
        refine Real.log_nonpos (by positivity) ?_
        rw [div_le_one (by linarith)]
        linarith
      have hdiv : 0 ≤ MarkovMixing.lambdaStar P / (1 - MarkovMixing.lambdaStar P) :=
        div_nonneg hq_nonneg (by linarith)
      rw [hrel]
      have := mul_nonpos_of_nonneg_of_nonpos hdiv hK
      linarith
    · have hTne : T ≠ 0 := by
        intro h
        obtain ⟨r, l, hl, hlne, rfl⟩ := hSne
        have hz := abs_pow_le P π hπ hl hlne 0
        rw [h] at hTmem
        simp at hz
        linarith
      have hTpos : (0:ℝ) < (T:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hTne
      set b : ℝ := (2*ε) ^ ((T:ℝ)⁻¹) with hb_def
      have hb0 : 0 < b := Real.rpow_pos_of_pos (by linarith) _
      have hb1 : b < 1 := Real.rpow_lt_one (by linarith) (by linarith) (inv_pos.mpr hTpos)
      have hqb : MarkovMixing.lambdaStar P ≤ b := by
        refine csSup_le hSne ?_
        rintro r ⟨l, hl, hlne, rfl⟩
        refine root_bound hTne (by linarith) (abs_nonneg l) ?_
        calc |l| ^ T ≤ 2 * distStationary P π T := abs_pow_le P π hπ hl hlne T
          _ ≤ 2 * ε := by linarith
      have hK0 : 0 < Real.log (1 / (2*ε)) := by
        refine Real.log_pos ?_
        rw [lt_div_iff₀ (by linarith)]
        linarith
      have hlogb : Real.log b = -(Real.log (1 / (2*ε)) / T) := by
        rw [hb_def, Real.log_rpow (by linarith), one_div, Real.log_inv]
        field_simp
      have hL : Real.log (1 / (2*ε)) / T ≤ (1 - b)/b := by
        have h1 : Real.log (1/b) ≤ 1/b - 1 := Real.log_le_sub_one_of_pos (by positivity)
        rw [one_div, Real.log_inv, hlogb] at h1
        have h2 : Real.log (1 / (2*ε)) / T ≤ b⁻¹ - 1 := by linarith
        calc Real.log (1 / (2*ε)) / T ≤ b⁻¹ - 1 := h2
          _ = (1-b)/b := by field_simp
      have hmono : MarkovMixing.lambdaStar P / (1 - MarkovMixing.lambdaStar P) ≤ b / (1-b) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith
      have hKb : Real.log (1 / (2*ε)) * b ≤ (1 - b) * T := by
        rw [div_le_div_iff₀ hTpos hb0] at hL
        linarith
      have hub : b/(1-b) * Real.log (1 / (2*ε)) ≤ (T:ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 1 - b)]
        nlinarith
      rw [hrel]
      calc MarkovMixing.lambdaStar P / (1 - MarkovMixing.lambdaStar P) * Real.log (1 / (2*ε))
          ≤ b/(1-b) * Real.log (1 / (2*ε)) := mul_le_mul_of_nonneg_right hmono hK0.le
        _ ≤ (T:ℝ) := hub
  · have hempty : {r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hSne
    have hq : MarkovMixing.lambdaStar P = 0 := by
      show sSup {r : ℝ | ∃ l : ℝ, IsEigenvalue P l ∧ l ≠ 1 ∧ r = |l|} = 0
      rw [hempty, Real.sSup_empty]
    have hrel : MarkovMixing.relaxationTime P = 1 := by
      show (1 - MarkovMixing.lambdaStar P)⁻¹ = 1
      rw [hq]; norm_num
    rw [hrel]
    simpa using hTnn
