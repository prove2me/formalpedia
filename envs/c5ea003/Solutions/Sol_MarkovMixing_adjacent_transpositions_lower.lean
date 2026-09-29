-- Prove2me | solution 1 for MarkovMixing.adjacent_transpositions_lower
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-23T06:32:40.619202+00:00
-- url     : https://prove2.me/submissions/7d855bd5-043c-4254-a93b-53789e6a0882

import Definitions.Def_mm_shuffle
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_relaxation_lower
import Theorems.Thm_MarkovMixing_eigenvalue_basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# An `n³` lower bound for random adjacent transpositions (LPW §16.1.3)
-/

namespace MarkovMixing

noncomputable section
open scoped BigOperators
open Finset

/-! ### Generic facts about random walks on a group -/

section GroupWalk

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

private lemma gw_row_sum (μ : G → ℝ) (hμ : IsDist μ) (a : G) :
    ∑ b, groupWalk μ a b = 1 := by
  rw [← hμ.2]
  exact Fintype.sum_equiv (Equiv.mulRight a⁻¹) (fun b => groupWalk μ a b) μ (fun b => rfl)

private lemma gw_col_sum (μ : G → ℝ) (hμ : IsDist μ) (b : G) :
    ∑ a, groupWalk μ a b = 1 := by
  rw [← hμ.2]
  exact Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulLeft b))
    (fun a => groupWalk μ a b) μ (fun a => rfl)

private lemma gw_stochastic (μ : G → ℝ) (hμ : IsDist μ) : IsStochastic (groupWalk μ) :=
  ⟨fun a b => hμ.1 _, gw_row_sum μ hμ⟩

private lemma gw_stationary (μ : G → ℝ) (hμ : IsDist μ) :
    IsStationary (groupWalk μ) (uniformDist G) := by
  have hN : (0 : ℝ) < (Fintype.card G : ℝ) := by
    have : 0 < Fintype.card G := Fintype.card_pos
    exact_mod_cast this
  refine ⟨⟨fun x => by simp only [uniformDist]; positivity, ?_⟩, ?_⟩
  · simp only [uniformDist]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · ext b
    simp only [Matrix.vecMul, dotProduct, uniformDist]
    rw [← Finset.mul_sum, gw_col_sum μ hμ, mul_one]

private lemma gw_detailed (μ : G → ℝ) (hsym : ∀ g : G, μ g⁻¹ = μ g) :
    DetailedBalance (groupWalk μ) (uniformDist G) := by
  intro x y
  simp only [uniformDist, groupWalk]
  congr 1
  rw [← hsym (y * x⁻¹)]
  congr 1
  group

private lemma gw_transl (μ : G → ℝ) (a b ρ : G) :
    groupWalk μ (a * ρ) (b * ρ) = groupWalk μ a b := by
  simp only [groupWalk]
  congr 1
  group

private lemma gw_pow_nonneg (μ : G → ℝ) (hμ : IsDist μ) :
    ∀ (t : ℕ) (x y : G), 0 ≤ ((groupWalk μ) ^ t) x y := by
  intro t
  induction t with
  | zero => intro x y; rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ t ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih x z) (hμ.1 _)

private lemma gw_pow_transl (μ : G → ℝ) : ∀ (t : ℕ) (a b ρ : G),
    ((groupWalk μ) ^ t) (a * ρ) (b * ρ) = ((groupWalk μ) ^ t) a b := by
  intro t
  induction t with
  | zero =>
      intro a b ρ
      rw [pow_zero, Matrix.one_apply, Matrix.one_apply]
      by_cases h : a = b
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (fun hc => h (mul_right_cancel hc))]
  | succ t ih =>
      intro a b ρ
      have hL : ((groupWalk μ) ^ (t + 1)) (a * ρ) (b * ρ)
          = ∑ w, ((groupWalk μ) ^ t) (a * ρ) w * groupWalk μ w (b * ρ) := by
        rw [pow_succ, Matrix.mul_apply]
      have hR : ((groupWalk μ) ^ (t + 1)) a b
          = ∑ w, ((groupWalk μ) ^ t) a w * groupWalk μ w b := by
        rw [pow_succ, Matrix.mul_apply]
      rw [hL, hR, ← Equiv.sum_comp (Equiv.mulRight ρ)
        (fun w => ((groupWalk μ) ^ t) (a * ρ) w * groupWalk μ w (b * ρ))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [Equiv.coe_mulRight]
      rw [ih a w ρ, gw_transl]

private lemma gw_pow_add_pos (μ : G → ℝ) (hμ : IsDist μ) {t₁ t₂ : ℕ} {a b c : G}
    (h1 : 0 < ((groupWalk μ) ^ t₁) a b) (h2 : 0 < ((groupWalk μ) ^ t₂) b c) :
    0 < ((groupWalk μ) ^ (t₁ + t₂)) a c := by
  rw [pow_add, Matrix.mul_apply]
  refine lt_of_lt_of_le (mul_pos h1 h2) ?_
  exact Finset.single_le_sum
    (f := fun w => ((groupWalk μ) ^ t₁) a w * ((groupWalk μ) ^ t₂) w c)
    (fun w _ => mul_nonneg (gw_pow_nonneg μ hμ t₁ a w) (gw_pow_nonneg μ hμ t₂ w c))
    (Finset.mem_univ b)

private lemma gw_aperiodic (μ : G → ℝ) (h1 : 0 < μ 1) : Aperiodic (groupWalk μ) := by
  intro x
  have hx : (1 : ℕ) ∈ returnSet (groupWalk μ) x := by
    refine ⟨le_refl 1, ?_⟩
    rw [pow_one]
    simpa only [groupWalk, mul_inv_cancel] using h1
  have hset : {d : ℕ | ∀ t ∈ returnSet (groupWalk μ) x, d ∣ t} = {1} := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => Nat.dvd_one.mp (h 1 hx), fun h t _ => by rw [h]; exact one_dvd t⟩
  rw [period, hset, csSup_singleton]

end GroupWalk

/-! ### The adjacent-transposition increment distribution -/

section AdjDist

variable {m : ℕ}

/-- The `i`-th adjacent transposition of `Fin (m+1)`. -/
private def sw (m : ℕ) (i : Fin m) : Equiv.Perm (Fin (m + 1)) :=
  Equiv.swap i.castSucc i.succ

private lemma sw_ne_one (i : Fin m) : sw m i ≠ 1 := by
  intro hc
  have h := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => (e i.castSucc).val) hc
  simp only [sw, Equiv.swap_apply_left, Equiv.Perm.one_apply, Fin.val_succ,
    Fin.coe_castSucc] at h
  omega

private lemma sw_inv (i : Fin m) : (sw m i)⁻¹ = sw m i := by
  rw [sw, Equiv.swap_inv]

private lemma sw_inj : Function.Injective (sw m) := by
  intro i j h
  have key := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => (e i.castSucc).val) h
  simp only [sw, Equiv.swap_apply_left] at key
  by_cases h1 : i.castSucc = j.castSucc
  · exact Fin.castSucc_inj.mp h1
  · by_cases h2 : i.castSucc = j.succ
    · rw [h2, Equiv.swap_apply_right] at key
      have e1 := congrArg Fin.val h2
      simp only [Fin.coe_castSucc, Fin.val_succ] at e1 key
      exact Fin.ext (by omega)
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at key
      simp only [Fin.coe_castSucc, Fin.val_succ] at key
      exact Fin.ext (by omega)

private lemma adj_one (m : ℕ) : adjacentTranspositionDist (m + 1) 1 = 1 / 2 := by
  simp only [adjacentTranspositionDist, if_pos]

private lemma adj_sw (m : ℕ) (i : Fin m) :
    adjacentTranspositionDist (m + 1) (sw m i) = 1 / (2 * (m : ℝ)) := by
  have hfin : (⟨(i.castSucc.val + 1) % (m + 1), Nat.mod_lt _ i.castSucc.pos⟩ : Fin (m + 1))
      = i.succ := by
    refine Fin.ext ?_
    simp only [Fin.coe_castSucc, Fin.val_succ]
    exact Nat.mod_eq_of_lt (by omega)
  have hex : ∃ i' : Fin (m + 1), i'.val + 1 < m + 1 ∧
      sw m i = Equiv.swap i' ⟨(i'.val + 1) % (m + 1), Nat.mod_lt _ i'.pos⟩ := by
    refine ⟨i.castSucc, by simp only [Fin.coe_castSucc]; omega, ?_⟩
    rw [hfin]
    rfl
  simp only [adjacentTranspositionDist, if_neg (sw_ne_one i), if_pos hex]
  push_cast
  ring_nf

private lemma adj_zero (m : ℕ) {g : Equiv.Perm (Fin (m + 1))} (hg1 : g ≠ 1)
    (hgs : ∀ i : Fin m, g ≠ sw m i) : adjacentTranspositionDist (m + 1) g = 0 := by
  simp only [adjacentTranspositionDist, if_neg hg1]
  rw [if_neg]
  rintro ⟨i', hi', heq⟩
  have hlt : i'.val < m := by omega
  have e1 : (⟨i'.val, hlt⟩ : Fin m).castSucc = i' := Fin.ext rfl
  have e2 : (⟨i'.val, hlt⟩ : Fin m).succ
      = (⟨(i'.val + 1) % (m + 1), Nat.mod_lt _ i'.pos⟩ : Fin (m + 1)) :=
    Fin.ext (by simp only [Fin.val_succ]; exact (Nat.mod_eq_of_lt (by omega)).symm)
  exact hgs ⟨i'.val, hlt⟩ (by rw [heq, sw, e1, e2])

private lemma adj_nonneg (m : ℕ) (g : Equiv.Perm (Fin (m + 1))) :
    0 ≤ adjacentTranspositionDist (m + 1) g := by
  have hc : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  simp only [adjacentTranspositionDist]
  split_ifs
  · norm_num
  · rw [hc]; positivity
  · exact le_refl 0

private lemma adj_sum (m : ℕ) (F : Equiv.Perm (Fin (m + 1)) → ℝ) :
    ∑ h, adjacentTranspositionDist (m + 1) h * F h
      = (1 / 2) * F 1 + (1 / (2 * (m : ℝ))) * ∑ i : Fin m, F (sw m i) := by
  classical
  have hsub : (insert (1 : Equiv.Perm (Fin (m + 1))) (Finset.univ.image (sw m)))
      ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ x ∈ (Finset.univ : Finset (Equiv.Perm (Fin (m + 1)))),
      x ∉ insert (1 : Equiv.Perm (Fin (m + 1))) (Finset.univ.image (sw m)) →
      adjacentTranspositionDist (m + 1) x * F x = 0 := by
    intro x _ hx
    rw [Finset.mem_insert] at hx
    push_neg at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [adj_zero m hx1 (fun i hc =>
      hx2 (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hc.symm⟩)), zero_mul]
  rw [← Finset.sum_subset hsub hzero]
  have hnotmem : (1 : Equiv.Perm (Fin (m + 1))) ∉ Finset.univ.image (sw m) := by
    intro hc
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hc
    exact sw_ne_one i hi
  rw [Finset.sum_insert hnotmem, adj_one,
    Finset.sum_image (fun a _ b _ h => sw_inj h)]
  rw [Finset.mul_sum]
  refine congrArg (fun z => (1 / 2) * F 1 + z) ?_
  exact Finset.sum_congr rfl fun i _ => by rw [adj_sw]

private lemma adj_isDist (m : ℕ) (hm : 1 ≤ m) : IsDist (adjacentTranspositionDist (m + 1)) := by
  refine ⟨adj_nonneg m, ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := adj_sum m (fun _ => (1 : ℝ))
  simp only [mul_one] at h
  rw [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp
  norm_num

private lemma adj_symm (m : ℕ) (g : Equiv.Perm (Fin (m + 1))) :
    adjacentTranspositionDist (m + 1) g⁻¹ = adjacentTranspositionDist (m + 1) g := by
  by_cases h1 : g = 1
  · rw [h1, inv_one]
  · by_cases h2 : ∃ i, g = sw m i
    · obtain ⟨i, rfl⟩ := h2
      rw [sw_inv]
    · push_neg at h2
      rw [adj_zero m h1 h2, adj_zero m (by simpa using h1) ?_]
      intro i hc
      exact h2 i (by rw [← sw_inv i, ← hc, inv_inv])

end AdjDist

/-! ### The cosine sequence and summation by parts -/

section Cosines

/-- `c_k = cos(π(2k+1)/(2n))`, the discrete cosine used by Wilson's method. -/
private def cc (n : ℕ) (k : ℕ) : ℝ :=
  Real.cos (Real.pi * (2 * (k : ℝ) + 1) / (2 * (n : ℝ)))

/-- The backward difference, with `dd n 0 = 0`. -/
private def dd (n : ℕ) (k : ℕ) : ℝ := cc n k - cc n (k - 1)

private lemma dd_zero (n : ℕ) : dd n 0 = 0 := by simp [dd]

private lemma dd_succ (n : ℕ) (j : ℕ) : dd n (j + 1) = cc n (j + 1) - cc n j := by
  simp [dd]

private lemma cc_rec (n : ℕ) (hn : 0 < n) (j : ℕ) :
    cc n (j + 2) + cc n j = 2 * Real.cos (Real.pi / n) * cc n (j + 1) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 := Real.cos_add_cos (Real.pi * (2 * ((j + 2 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)))
    (Real.pi * (2 * ((j : ℕ) : ℝ) + 1) / (2 * (n : ℝ)))
  rw [show (Real.pi * (2 * ((j + 2 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))
        + Real.pi * (2 * ((j : ℕ) : ℝ) + 1) / (2 * (n : ℝ))) / 2
      = Real.pi * (2 * ((j + 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) from by
        push_cast; field_simp; ring,
    show (Real.pi * (2 * ((j + 2 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))
        - Real.pi * (2 * ((j : ℕ) : ℝ) + 1) / (2 * (n : ℝ))) / 2
      = Real.pi / (n : ℝ) from by push_cast; field_simp; ring] at h1
  simp only [cc]
  rw [h1]
  ring

private lemma cc_bd (n : ℕ) (hn : 0 < n) :
    cc n 1 + cc n 0 = 2 * Real.cos (Real.pi / n) * cc n 0 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 := Real.cos_add_cos (Real.pi * (2 * ((1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)))
    (Real.pi * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)))
  rw [show (Real.pi * (2 * ((1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))
        + Real.pi * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))) / 2
      = Real.pi / (n : ℝ) from by push_cast; field_simp; ring,
    show (Real.pi * (2 * ((1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))
        - Real.pi * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ))) / 2
      = Real.pi * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) from by
        push_cast; field_simp; ring] at h1
  simp only [cc]
  rw [h1]

private lemma cc_top (n : ℕ) (hn : 0 < n) : cc n n = cc n (n - 1) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; norm_num
  simp only [cc]
  rw [show Real.pi * (2 * ((n : ℕ) : ℝ) + 1) / (2 * (n : ℝ))
      = 2 * Real.pi - Real.pi * (2 * ((n - 1 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) from by
        rw [hc]; field_simp; ring]
  rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring

private lemma cc_key (n : ℕ) (hn : 0 < n) (i : ℕ) :
    (cc n (i + 1) - cc n i) - dd n i = (2 * Real.cos (Real.pi / n) - 2) * cc n i := by
  rcases i with _ | j
  · rw [dd_zero]
    have := cc_bd n hn
    linarith
  · rw [dd_succ]
    have := cc_rec n hn j
    have h2 : j + 1 + 1 = j + 2 := rfl
    rw [h2]
    linarith

private lemma sbp (n : ℕ) (hn : 0 < n) (b : ℕ → ℝ) :
    ∑ i ∈ range n, (cc n (i + 1) - cc n i) * (b i - b (i + 1))
      = (2 * Real.cos (Real.pi / n) - 2) * ∑ i ∈ range n, cc n i * b i := by
  have hFn : dd n n * b n = 0 := by rw [dd, cc_top n hn]; ring
  have hshift : ∑ i ∈ range n, dd n (i + 1) * b (i + 1)
      = ∑ i ∈ range n, dd n i * b i := by
    have h1 : ∑ i ∈ range (n + 1), dd n i * b i
        = (∑ i ∈ range n, dd n (i + 1) * b (i + 1)) + dd n 0 * b 0 :=
      Finset.sum_range_succ' (fun i => dd n i * b i) n
    have h2 : ∑ i ∈ range (n + 1), dd n i * b i
        = (∑ i ∈ range n, dd n i * b i) + dd n n * b n :=
      Finset.sum_range_succ (fun i => dd n i * b i) n
    rw [dd_zero, zero_mul] at h1
    rw [hFn] at h2
    linarith
  have hsplit : ∑ i ∈ range n, (cc n (i + 1) - cc n i) * (b i - b (i + 1))
      = (∑ i ∈ range n, (cc n (i + 1) - cc n i) * b i)
        - ∑ i ∈ range n, dd n (i + 1) * b (i + 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [dd_succ]; ring
  rw [hsplit, hshift, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (b i) * (cc_key n hn i)

end Cosines

/-! ### The eigenfunction -/

section Eigen

variable {m : ℕ}

/-- Wilson's test function `Φ(σ) = ∑_j c(j) c(σ j)`. -/
private def PhiF (m : ℕ) (σ : Equiv.Perm (Fin (m + 1))) : ℝ :=
  ∑ j : Fin (m + 1), cc (m + 1) j.val * cc (m + 1) (σ j).val

private lemma phi_inv (σ : Equiv.Perm (Fin (m + 1))) : PhiF m σ⁻¹ = PhiF m σ := by
  simp only [PhiF]
  rw [← Equiv.sum_comp σ (fun j => cc (m + 1) j.val * cc (m + 1) (σ⁻¹ j).val)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show σ⁻¹ (σ j) = j from by simp]
  ring

private lemma castSucc_ne_succ (i : Fin m) : i.castSucc ≠ i.succ := by
  intro hc
  have := congrArg Fin.val hc
  simp only [Fin.val_castSucc, Fin.val_succ] at this
  omega

private lemma phi_swap (m : ℕ) (i : Fin m) (σ : Equiv.Perm (Fin (m + 1))) :
    PhiF m (sw m i * σ) - PhiF m σ
      = (cc (m + 1) (i.val + 1) - cc (m + 1) i.val)
        * (cc (m + 1) ((σ⁻¹ i.castSucc).val) - cc (m + 1) ((σ⁻¹ i.succ).val)) := by
  classical
  have hdiff : PhiF m (sw m i * σ) - PhiF m σ
      = ∑ j : Fin (m + 1),
          cc (m + 1) j.val * (cc (m + 1) ((sw m i) (σ j)).val - cc (m + 1) (σ j).val) := by
    simp only [PhiF, Equiv.Perm.mul_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hab : σ⁻¹ i.castSucc ≠ σ⁻¹ i.succ := by
    intro hc
    exact castSucc_ne_succ i (by simpa using congrArg (fun x => σ x) hc)
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin (m + 1))),
      x ∉ ({σ⁻¹ i.castSucc, σ⁻¹ i.succ} : Finset (Fin (m + 1))) →
      cc (m + 1) x.val * (cc (m + 1) ((sw m i) (σ x)).val - cc (m + 1) (σ x).val) = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    push_neg at hx
    have h1 : σ x ≠ i.castSucc := fun hc => hx.1 (by rw [← hc]; simp)
    have h2 : σ x ≠ i.succ := fun hc => hx.2 (by rw [← hc]; simp)
    rw [sw, Equiv.swap_apply_of_ne_of_ne h1 h2]
    ring
  rw [hdiff, ← Finset.sum_subset (Finset.subset_univ
    ({σ⁻¹ i.castSucc, σ⁻¹ i.succ} : Finset (Fin (m + 1)))) hzero, Finset.sum_pair hab]
  rw [show σ (σ⁻¹ i.castSucc) = i.castSucc from by simp,
    show σ (σ⁻¹ i.succ) = i.succ from by simp, sw, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  simp only [Fin.val_castSucc, Fin.val_succ]
  ring

/-- The eigenvalue attached to `Φ`. -/
private def lam (m : ℕ) : ℝ := 1 - (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) / m

private lemma phi_step (m : ℕ) (hm : 1 ≤ m) (σ : Equiv.Perm (Fin (m + 1))) :
    ∑ τ, groupWalk (adjacentTranspositionDist (m + 1)) σ τ * PhiF m τ
      = lam m * PhiF m σ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (0 : ℕ) < m + 1 := by omega
  -- reindex by the increment
  have hre : ∑ τ, groupWalk (adjacentTranspositionDist (m + 1)) σ τ * PhiF m τ
      = ∑ h, adjacentTranspositionDist (m + 1) h * PhiF m (h * σ) := by
    rw [← Equiv.sum_comp (Equiv.mulRight σ)
      (fun τ => groupWalk (adjacentTranspositionDist (m + 1)) σ τ * PhiF m τ)]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Equiv.coe_mulRight, groupWalk]
    congr 2
    group
  rw [hre, adj_sum m (fun h => PhiF m (h * σ)), one_mul]
  -- the sum over generators
  obtain ⟨bb, hbb⟩ : ∃ bb : ℕ → ℝ, ∀ k : ℕ,
      bb k = cc (m + 1) ((σ⁻¹ ⟨k % (m + 1), Nat.mod_lt _ hm1⟩).val) := ⟨_, fun _ => rfl⟩
  have hbfin : ∀ j : Fin (m + 1), bb j.val = cc (m + 1) ((σ⁻¹ j).val) := by
    intro j
    rw [hbb]
    congr 3
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
  have hb1 : ∀ i : Fin m, bb i.val = cc (m + 1) ((σ⁻¹ i.castSucc).val) := by
    intro i
    have := hbfin i.castSucc
    rwa [Fin.val_castSucc] at this
  have hb2 : ∀ i : Fin m, bb (i.val + 1) = cc (m + 1) ((σ⁻¹ i.succ).val) := by
    intro i
    have := hbfin i.succ
    rwa [Fin.val_succ] at this
  have hgen : ∑ i : Fin m, PhiF m (sw m i * σ)
      = (m : ℝ) * PhiF m σ
        + ∑ i ∈ range m, (cc (m + 1) (i + 1) - cc (m + 1) i) * (bb i - bb (i + 1)) := by
    have hstep : ∀ i : Fin m, PhiF m (sw m i * σ)
        = PhiF m σ
          + (cc (m + 1) (i.val + 1) - cc (m + 1) i.val) * (bb i.val - bb (i.val + 1)) := by
      intro i
      rw [hb1, hb2, ← phi_swap m i σ]
      ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun k => (cc (m + 1) (k + 1) - cc (m + 1) k) * (bb k - bb (k + 1))) m
  -- extend the range-`m` sum to a range-`(m+1)` sum and apply summation by parts
  have hlast : (cc (m + 1) (m + 1) - cc (m + 1) m) * (bb m - bb (m + 1)) = 0 := by
    have := cc_top (m + 1) hm1
    simp only [Nat.add_sub_cancel] at this
    rw [this]
    ring
  have hext : ∑ i ∈ range m, (cc (m + 1) (i + 1) - cc (m + 1) i) * (bb i - bb (i + 1))
      = ∑ i ∈ range (m + 1), (cc (m + 1) (i + 1) - cc (m + 1) i) * (bb i - bb (i + 1)) := by
    rw [Finset.sum_range_succ, hlast, add_zero]
  have hphi : ∑ i ∈ range (m + 1), cc (m + 1) i * bb i = PhiF m σ := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => cc (m + 1) k * bb k) (m + 1)]
    rw [← phi_inv σ]
    simp only [PhiF]
    exact Finset.sum_congr rfl fun j _ => by rw [hbfin j]
  rw [hgen, hext, sbp (m + 1) hm1 bb, hphi]
  have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcast, lam]
  field_simp
  ring

end Eigen

/-! ### The spectrum of a finite chain is finite -/

section Spectrum

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

private lemma eig_isRoot (P : Matrix V V ℝ) {lam : ℝ} (h : IsEigenvalue P lam) :
    P.charpoly.IsRoot lam := by
  obtain ⟨f, hf0, hf⟩ := h
  have hs : (Matrix.scalar V lam) = lam • (1 : Matrix V V ℝ) := by
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  have hmv : ((lam : ℝ) • (1 : Matrix V V ℝ)).mulVec f = lam • f := by
    ext x
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq]
  have h1 : (Matrix.scalar V lam - P).mulVec f = 0 := by
    rw [Matrix.sub_mulVec, hs, hmv, hf, sub_self]
  have h2 : (Matrix.scalar V lam - P).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨f, hf0, h1⟩
  rw [Polynomial.IsRoot, Matrix.eval_charpoly]
  exact h2

private lemma lambdaStar_bounds (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : Irreducible P) (hap : Aperiodic P)
    (lam0 : ℝ) (heig : IsEigenvalue P lam0) (hne : lam0 ≠ 1) :
    lam0 ≤ lambdaStar P ∧ lambdaStar P < 1 := by
  have hfin : {x : ℝ | P.charpoly.IsRoot x}.Finite :=
    Polynomial.finite_setOf_isRoot (P.charpoly_monic.ne_zero)
  have hSsub : {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}
      ⊆ (fun x => |x|) '' {x : ℝ | P.charpoly.IsRoot x} := by
    rintro r ⟨lam, hl, hl1, rfl⟩
    exact ⟨lam, eig_isRoot P hl, rfl⟩
  have hSfin : {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}.Finite :=
    Set.Finite.subset (hfin.image _) hSsub
  have hSne : {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}.Nonempty :=
    ⟨|lam0|, lam0, heig, hne, rfl⟩
  have hmem : lambdaStar P ∈ {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|} :=
    hSne.csSup_mem hSfin
  obtain ⟨lam1, hl1e, hl1ne, hl1eq⟩ := hmem
  have hb := eigenvalue_basic P hP
  have habs : |lam1| ≤ 1 := hb.1 lam1 hl1e
  refine ⟨le_trans (le_abs_self lam0) (le_csSup hSfin.bddAbove ⟨lam0, heig, hne, rfl⟩), ?_⟩
  rcases lt_or_eq_of_le habs with h | h
  · rw [hl1eq]; exact h
  · exfalso
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp h with h1 | h1
    · exact hl1ne h1
    · exact hb.2.2 hirr hap (h1 ▸ hl1e)

end Spectrum

/-! ### Chain properties and positivity of `Φ` -/

section Chain

private lemma adj_irred (m : ℕ) (hm : 1 ≤ m) :
    Irreducible (groupWalk (adjacentTranspositionDist (m + 1))) := by
  have hμ := adj_isDist m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hself : ∀ σ : Equiv.Perm (Fin (m + 1)),
      0 < groupWalk (adjacentTranspositionDist (m + 1)) σ σ := by
    intro σ
    show 0 < adjacentTranspositionDist (m + 1) (σ * σ⁻¹)
    rw [mul_inv_cancel, adj_one]
    norm_num
  have key : ∀ g : Equiv.Perm (Fin (m + 1)),
      ∃ t : ℕ, 0 < ((groupWalk (adjacentTranspositionDist (m + 1))) ^ t) 1 g := by
    intro g
    have hmem : g ∈ Submonoid.closure
        (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top g
    refine Submonoid.closure_induction ?_ ?_ ?_ hmem
    · rintro x ⟨i, rfl⟩
      refine ⟨1, ?_⟩
      rw [pow_one]
      show 0 < adjacentTranspositionDist (m + 1) (Equiv.swap i.castSucc i.succ * 1⁻¹)
      rw [inv_one, mul_one, show Equiv.swap i.castSucc i.succ = sw m i from rfl, adj_sw]
      positivity
    · exact ⟨0, by rw [pow_zero, Matrix.one_apply_eq]; norm_num⟩
    · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
      refine ⟨t₂ + t₁, ?_⟩
      have h₁' : 0 < ((groupWalk (adjacentTranspositionDist (m + 1))) ^ t₁) b (a * b) := by
        have h := gw_pow_transl (adjacentTranspositionDist (m + 1)) t₁ 1 a b
        rw [one_mul] at h
        rw [h]
        exact h₁
      exact gw_pow_add_pos _ hμ h₂ h₁'
  intro x y
  obtain ⟨t, ht⟩ := key (y * x⁻¹)
  refine ⟨t, ?_⟩
  have h := gw_pow_transl (adjacentTranspositionDist (m + 1)) t 1 (y * x⁻¹) x
  rw [one_mul, inv_mul_cancel_right] at h
  rw [h]
  exact ht

private lemma adj_aper (m : ℕ) : Aperiodic (groupWalk (adjacentTranspositionDist (m + 1))) := by
  refine gw_aperiodic _ ?_
  rw [adj_one]
  norm_num

private lemma cc_zero_pos (n : ℕ) (hn : 2 ≤ n) : 0 < cc n 0 := by
  have hpi := Real.pi_pos
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  simp only [cc]
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
  · have : (0 : ℝ) < Real.pi * (2 * ((0 : ℕ) : ℝ) + 1) / (2 * (n : ℝ)) := by
      push_cast
      positivity
    linarith
  · rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (n : ℝ))]
    push_cast
    nlinarith

private lemma phi_one_pos (m : ℕ) (hm : 1 ≤ m) : 0 < PhiF m 1 := by
  have h0 : 0 < cc (m + 1) 0 := cc_zero_pos (m + 1) (by omega)
  have hterm : ∀ j : Fin (m + 1), 0 ≤ cc (m + 1) j.val * cc (m + 1) ((1 : Equiv.Perm (Fin (m+1))) j).val := by
    intro j
    simp only [Equiv.Perm.one_apply]
    exact mul_self_nonneg _
  have hle : cc (m + 1) ((0 : Fin (m + 1))).val
      * cc (m + 1) ((1 : Equiv.Perm (Fin (m+1))) (0 : Fin (m + 1))).val ≤ PhiF m 1 :=
    Finset.single_le_sum (f := fun j : Fin (m + 1) =>
      cc (m + 1) j.val * cc (m + 1) ((1 : Equiv.Perm (Fin (m+1))) j).val)
      (fun j _ => hterm j) (Finset.mem_univ _)
  have hval : ((0 : Fin (m + 1))).val = 0 := rfl
  simp only [Equiv.Perm.one_apply, hval] at hle
  nlinarith

end Chain

/-! ### The main estimate for `n ≥ 3` -/

section Main

private lemma main_bound (m : ℕ) (hm : 2 ≤ m) :
    ((m : ℝ) + 1) ^ 2 * (m : ℝ) / 16
      ≤ (tMix (groupWalk (adjacentTranspositionDist (m + 1)))
          (uniformDist (Equiv.Perm (Fin (m + 1)))) : ℝ) := by
  have hm1 : 1 ≤ m := by omega
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpipos := Real.pi_pos
  have hμ := adj_isDist m hm1
  have hstoch : IsStochastic (groupWalk (adjacentTranspositionDist (m + 1))) :=
    gw_stochastic _ hμ
  have hstat : IsStationary (groupWalk (adjacentTranspositionDist (m + 1)))
      (uniformDist (Equiv.Perm (Fin (m + 1)))) := gw_stationary _ hμ
  have hrev : DetailedBalance (groupWalk (adjacentTranspositionDist (m + 1)))
      (uniformDist (Equiv.Perm (Fin (m + 1)))) := gw_detailed _ (adj_symm m)
  have hirr := adj_irred m hm1
  have hap := adj_aper m
  -- `Φ` is an eigenfunction
  have heigfun : (groupWalk (adjacentTranspositionDist (m + 1))).mulVec (PhiF m)
      = (lam m) • (PhiF m) := by
    funext σ
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    exact phi_step m hm1 σ
  have hPhi0 : PhiF m ≠ 0 := by
    intro hc
    have h1 : PhiF m 1 = 0 := by simp [hc]
    have h2 := phi_one_pos m hm1
    rw [h1] at h2
    exact lt_irrefl 0 h2
  have heig : IsEigenvalue (groupWalk (adjacentTranspositionDist (m + 1))) (lam m) :=
    ⟨PhiF m, hPhi0, heigfun⟩
  -- the spectral gap of the cosine eigenfunction
  have hxpos : 0 < Real.pi / ((m : ℝ) + 1) := by positivity
  have hxlt : Real.pi / ((m : ℝ) + 1) < 2 * Real.pi := by
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < (m : ℝ) + 1)]
    nlinarith
  have hcoslt : Real.cos (Real.pi / ((m : ℝ) + 1)) < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one (Real.pi / ((m : ℝ) + 1))) with h | h
    · exact h
    · exfalso
      have h2 := (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith : -(2 * Real.pi) < Real.pi / ((m : ℝ) + 1)) hxlt).mp h
      linarith
  have hKpos : 0 < 1 - Real.cos (Real.pi / ((m : ℝ) + 1)) := by linarith
  have hne1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have hKle : (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) * (2 * ((m : ℝ) + 1) ^ 2)
      ≤ Real.pi ^ 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := Real.pi / ((m : ℝ) + 1))
    calc (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) * (2 * ((m : ℝ) + 1) ^ 2)
        ≤ ((Real.pi / ((m : ℝ) + 1)) ^ 2 / 2) * (2 * ((m : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = Real.pi ^ 2 := by field_simp
  have hlamne : lam m ≠ 1 := by
    rw [lam]
    intro hc
    have : (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) / (m : ℝ) = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · linarith
    · rw [h] at hmR; linarith
  obtain ⟨hle, hlt⟩ := lambdaStar_bounds _ hstoch hirr hap (lam m) heig hlamne
  have hgap : 0 < 1 - lambdaStar (groupWalk (adjacentTranspositionDist (m + 1))) := by
    linarith
  have hgapu : 1 - lambdaStar (groupWalk (adjacentTranspositionDist (m + 1)))
      ≤ Real.pi ^ 2 / (2 * (m : ℝ) * ((m : ℝ) + 1) ^ 2) := by
    have h1 : 1 - lambdaStar (groupWalk (adjacentTranspositionDist (m + 1)))
        ≤ (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) / (m : ℝ) := by
      rw [lam] at hle; linarith
    have h2 : (1 - Real.cos (Real.pi / ((m : ℝ) + 1))) / (m : ℝ)
        ≤ Real.pi ^ 2 / (2 * (m : ℝ) * ((m : ℝ) + 1) ^ 2) := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hKle (by linarith : (0:ℝ) ≤ (m : ℝ))]
    linarith
  have hrelge : 2 * (m : ℝ) * ((m : ℝ) + 1) ^ 2 / Real.pi ^ 2
      ≤ relaxationTime (groupWalk (adjacentTranspositionDist (m + 1))) := by
    rw [relaxationTime, absSpectralGap]
    have h := one_div_le_one_div_of_le hgap hgapu
    rw [one_div, one_div] at h
    calc 2 * (m : ℝ) * ((m : ℝ) + 1) ^ 2 / Real.pi ^ 2
        = (Real.pi ^ 2 / (2 * (m : ℝ) * ((m : ℝ) + 1) ^ 2))⁻¹ := by
          rw [inv_div]
    _ ≤ _ := h
  -- numeric wrap-up
  have hQ : (18 : ℝ) ≤ (m : ℝ) * ((m : ℝ) + 1) ^ 2 := by nlinarith
  have hpi2 : Real.pi ^ 2 < 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hR2 : 0.2015 * ((m : ℝ) * ((m : ℝ) + 1) ^ 2)
      ≤ relaxationTime (groupWalk (adjacentTranspositionDist (m + 1))) := by
    refine le_trans ?_ hrelge
    rw [le_div_iff₀ (by positivity : (0:ℝ) < Real.pi ^ 2)]
    nlinarith
  have hR1 : (1 : ℝ) ≤ relaxationTime (groupWalk (adjacentTranspositionDist (m + 1))) := by
    nlinarith
  have hL : (0.6931471803 : ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
  have hrl := relaxation_lower (groupWalk (adjacentTranspositionDist (m + 1))) hstoch hirr hap
    (uniformDist (Equiv.Perm (Fin (m + 1)))) hstat hrev (1 / 4) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) / (2 * (1 / 4)) = 2 from by norm_num] at hrl
  have hfin : ((m : ℝ) + 1) ^ 2 * (m : ℝ) / 16
      ≤ (relaxationTime (groupWalk (adjacentTranspositionDist (m + 1))) - 1) * Real.log 2 := by
    nlinarith [mul_nonneg (by linarith :
        (0:ℝ) ≤ relaxationTime (groupWalk (adjacentTranspositionDist (m + 1))) - 1)
      (by linarith : (0:ℝ) ≤ Real.log 2 - 0.6931471803)]
  exact le_trans hfin hrl

end Main

/-! ### The case `n = 2` -/

section Small

private lemma perm2_card : Fintype.card (Equiv.Perm (Fin (1 + 1))) = 2 := by
  simp [Fintype.card_perm]

private lemma adj2_all (g : Equiv.Perm (Fin (1 + 1))) :
    adjacentTranspositionDist (1 + 1) g = 1 / 2 := by
  classical
  have hsw : (sw 1 0 : Equiv.Perm (Fin (1 + 1))) ≠ 1 := sw_ne_one 0
  have hcard : ({1, sw 1 0} : Finset (Equiv.Perm (Fin (1 + 1)))).card
      = Fintype.card (Equiv.Perm (Fin (1 + 1))) := by
    rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using hsw), Finset.card_singleton,
      perm2_card]
  have huniv : ({1, sw 1 0} : Finset (Equiv.Perm (Fin (1 + 1)))) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hg : g ∈ ({1, sw 1 0} : Finset (Equiv.Perm (Fin (1 + 1)))) := by
    rw [huniv]; exact Finset.mem_univ g
  rcases Finset.mem_insert.mp hg with h | h
  · rw [h, adj_one]
  · rw [Finset.mem_singleton.mp h, adj_sw]
    norm_num

private lemma small_bound :
    (1 : ℝ) / 4 ≤ (tMix (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) : ℝ) := by
  classical
  have hPval : ∀ σ τ : Equiv.Perm (Fin (1 + 1)),
      groupWalk (adjacentTranspositionDist (1 + 1)) σ τ = 1 / 2 :=
    fun σ τ => adj2_all _
  have hpi : ∀ y : Equiv.Perm (Fin (1 + 1)),
      uniformDist (Equiv.Perm (Fin (1 + 1))) y = 1 / 2 := by
    intro y
    simp only [uniformDist, perm2_card]
    norm_num
  -- the chain is already stationary after one step
  have hrow : ∀ x : Equiv.Perm (Fin (1 + 1)),
      rowDist (groupWalk (adjacentTranspositionDist (1 + 1))) 1 x
        = uniformDist (Equiv.Perm (Fin (1 + 1))) := by
    intro x
    funext y
    simp only [rowDist, pow_one, hPval, hpi]
  have htv : tvDist (uniformDist (Equiv.Perm (Fin (1 + 1))))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) = 0 := by
    simp only [tvDist, sub_self, abs_zero, ciSup_const]
  have hd1 : distStationary (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) 1 = 0 := by
    simp only [distStationary, hrow, htv, ciSup_const]
  -- at time zero the chain is far from stationarity
  have hbddA : ∀ μ ν : Equiv.Perm (Fin (1 + 1)) → ℝ,
      BddAbove (Set.range fun A : Finset (Equiv.Perm (Fin (1 + 1))) =>
        |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) := fun μ ν =>
    Set.Finite.bddAbove (Set.range fun A : Finset (Equiv.Perm (Fin (1 + 1))) =>
      |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have hstep : |∑ y ∈ ({1} : Finset (Equiv.Perm (Fin (1 + 1)))),
        rowDist (groupWalk (adjacentTranspositionDist (1 + 1))) 0 1 y
      - ∑ y ∈ ({1} : Finset (Equiv.Perm (Fin (1 + 1)))),
        uniformDist (Equiv.Perm (Fin (1 + 1))) y| = 1 / 2 := by
    rw [Finset.sum_singleton, Finset.sum_singleton, hpi]
    simp only [rowDist, pow_zero, Matrix.one_apply_eq]
    norm_num
  have h1 : (1 : ℝ) / 2 ≤ tvDist (rowDist (groupWalk (adjacentTranspositionDist (1 + 1))) 0 1)
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) := by
    rw [← hstep]
    exact le_ciSup (hbddA _ _) ({1} : Finset (Equiv.Perm (Fin (1 + 1))))
  have h2 : tvDist (rowDist (groupWalk (adjacentTranspositionDist (1 + 1))) 0 1)
      (uniformDist (Equiv.Perm (Fin (1 + 1))))
      ≤ distStationary (groupWalk (adjacentTranspositionDist (1 + 1)))
        (uniformDist (Equiv.Perm (Fin (1 + 1)))) 0 := by
    refine le_ciSup (Set.Finite.bddAbove (Set.range fun x : Equiv.Perm (Fin (1 + 1)) =>
      tvDist (rowDist (groupWalk (adjacentTranspositionDist (1 + 1))) 0 x)
        (uniformDist (Equiv.Perm (Fin (1 + 1))))).toFinite) 1
  -- conclude
  have hnem : {t : ℕ | distStationary (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) t ≤ 1 / 4}.Nonempty := by
    refine ⟨1, ?_⟩
    simp only [Set.mem_setOf_eq, hd1]
    norm_num
  have hmem : (tMix (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))))
      ∈ {t : ℕ | distStationary (groupWalk (adjacentTranspositionDist (1 + 1)))
        (uniformDist (Equiv.Perm (Fin (1 + 1)))) t ≤ 1 / 4} := Nat.sInf_mem hnem
  have hzero : (0 : ℕ) ∉ {t : ℕ | distStationary (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) t ≤ 1 / 4} := by
    simp only [Set.mem_setOf_eq, not_le]
    linarith
  have hge : 1 ≤ tMix (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) := by
    rcases Nat.eq_zero_or_pos (tMix (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1))))) with h | h
    · exact absurd (h ▸ hmem) hzero
    · exact h
  have : (1 : ℝ) ≤ (tMix (groupWalk (adjacentTranspositionDist (1 + 1)))
      (uniformDist (Equiv.Perm (Fin (1 + 1)))) : ℝ) := by exact_mod_cast hge
  linarith

end Small

end

end MarkovMixing

open MarkovMixing

/-- **§16.1.3** (LPW): for the lazy random adjacent transpositions shuffle
on `n` cards, `t_mix ≥ n²(n−1)/16`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 * ((n : ℝ) - 1) / 16 ≤
      (tMix (groupWalk (adjacentTranspositionDist n))
        (uniformDist (Equiv.Perm (Fin n))) : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.lt_or_ge m 2 with h | h
  · have hm : m = 1 := by omega
    subst hm
    refine le_trans ?_ small_bound
    norm_num
  · have hmain := main_bound m h
    have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hc]
    calc ((m : ℝ) + 1) ^ 2 * (((m : ℝ) + 1) - 1) / 16
        = ((m : ℝ) + 1) ^ 2 * (m : ℝ) / 16 := by ring
      _ ≤ _ := hmain
