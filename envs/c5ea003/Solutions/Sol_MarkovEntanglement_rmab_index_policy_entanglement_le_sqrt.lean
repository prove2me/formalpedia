-- Prove2me | solution 1 for MarkovEntanglement.rmab_index_policy_entanglement_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-31T00:49:17.513849+00:00
-- url     : https://prove2.me/submissions/467e5343-a369-41a8-8a6a-18f9614f81b3

import Definitions.Def_markov_entanglement_meanfield
import Theorems.Thm_MarkovEntanglement_meanFieldMap_piecewise_affine
import Theorems.Thm_MarkovEntanglement_rmab_entanglement_le_configuration_deviation
import Theorems.Thm_MarkovEntanglement_rmab_one_step_concentration
import Theorems.Thm_MarkovEntanglement_rmab_multi_step_concentration
import Theorems.Thm_MarkovEntanglement_rmab_local_stability

open scoped BigOperators
open MarkovEntanglement


variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ### Toolbox assembled from the milestone developments -/


private lemma abs_le_supNorm (v : S → ℝ) (x : S) : |v x| ≤ supNorm v := by
  unfold supNorm
  exact le_ciSup (f := fun z : S => |v z|)
    (Set.Finite.bddAbove (Set.finite_range fun z : S => |v z|)) x

private lemma supNorm_le {v : S → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x, |v x| ≤ c) :
    supNorm v ≤ c := by
  unfold supNorm
  exact Real.iSup_le h hc

private lemma supNorm_nonneg (v : S → ℝ) : 0 ≤ supNorm v := by
  unfold supNorm
  exact Real.iSup_nonneg fun x => abs_nonneg _

private lemma supNorm_self_zero (m : S → ℝ) : supNorm (fun x => m x - m x) = 0 := by
  refine le_antisymm (supNorm_le le_rfl fun x => by simp) (supNorm_nonneg _)

private lemma supNorm_sub_le (u v : S → ℝ) :
    supNorm (fun z => u z - v z) ≤ supNorm u + supNorm v := by
  refine supNorm_le (add_nonneg (supNorm_nonneg u) (supNorm_nonneg v)) fun z => ?_
  calc |u z - v z| ≤ |u z| + |v z| := abs_sub _ _
    _ ≤ supNorm u + supNorm v := add_le_add (abs_le_supNorm u z) (abs_le_supNorm v z)

private lemma supNorm_triangle (u v w : S → ℝ) :
    supNorm (fun x => u x - w x)
      ≤ supNorm (fun x => u x - v x) + supNorm (fun x => v x - w x) := by
  refine supNorm_le (add_nonneg (supNorm_nonneg _) (supNorm_nonneg _)) fun x => ?_
  calc |u x - w x| ≤ |u x - v x| + |v x - w x| := abs_sub_le _ _ _
    _ ≤ supNorm (fun x => u x - v x) + supNorm (fun x => v x - w x) :=
        add_le_add (abs_le_supNorm (fun x => u x - v x) x)
          (abs_le_supNorm (fun x => v x - w x) x)

private lemma min_lipschitz (a b a' b' : ℝ) :
    |min a b - min a' b'| ≤ max |a - a'| |b - b'| := by
  set c := max |a - a'| |b - b'| with hc
  have key : ∀ u v u' v' : ℝ, |u - u'| ≤ c → |v - v'| ≤ c →
      min u v - min u' v' ≤ c := by
    intro u v u' v' hu hv
    have h1 : u ≤ u' + c := by
      have := le_abs_self (u - u'); linarith
    have h2 : v ≤ v' + c := by
      have := le_abs_self (v - v'); linarith
    have h3 : min u v ≤ min (u' + c) (v' + c) := min_le_min h1 h2
    rw [min_add_add_right] at h3
    linarith
  have hA : |a - a'| ≤ c := le_max_left _ _
  have hB : |b - b'| ≤ c := le_max_right _ _
  have hA' : |a' - a| ≤ c := by rwa [abs_sub_comm]
  have hB' : |b' - b| ≤ c := by rwa [abs_sub_comm]
  rw [abs_sub_le_iff]
  exact ⟨key a b a' b' hA hB, key a' b' a b hA' hB'⟩

/-! ### The mean-field map preserves the simplex -/

private lemma max_zero_lipschitz (u v : ℝ) : |max 0 u - max 0 v| ≤ |u - v| := by
  have key : ∀ w z : ℝ, max 0 w - max 0 z ≤ |w - z| := by
    intro w z
    have h1 : w ≤ z + |w - z| := by
      have := le_abs_self (w - z); linarith
    have h2 : max 0 w ≤ max 0 (z + |w - z|) := max_le_max (le_refl 0) h1
    have h3 : max 0 (z + |w - z|) ≤ max 0 z + |w - z| := by
      refine max_le ?_ ?_
      · linarith [le_max_left 0 z, abs_nonneg (w - z)]
      · linarith [le_max_right 0 z]
    linarith
  rw [abs_sub_le_iff]
  refine ⟨key u v, ?_⟩
  have := key v u
  rwa [abs_sub_comm] at this

private lemma supNorm_smul_le (c : ℝ) (hc : 0 ≤ c) (v : S → ℝ) :
    supNorm (fun z => c * v z) ≤ c * supNorm v := by
  refine supNorm_le (mul_nonneg hc (supNorm_nonneg v)) fun z => ?_
  rw [abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_le_supNorm v z) hc

private lemma supNorm_smul_nonneg {c : ℝ} (hc : 0 ≤ c) (v : S → ℝ) :
    supNorm (fun z => c * v z) = c * supNorm v := by
  refine le_antisymm (supNorm_smul_le c hc v) ?_
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · rw [← hc0]
    simp [supNorm_nonneg]
  · have hcne : c ≠ 0 := ne_of_gt hcpos
    have hfun : v = fun z => (1 / c) * (c * v z) := by
      funext z
      field_simp
    have h1 : supNorm v ≤ (1 / c) * supNorm (fun z => c * v z) := by
      conv_lhs => rw [hfun]
      exact supNorm_smul_le (1 / c) (by positivity) _
    calc c * supNorm v ≤ c * ((1 / c) * supNorm (fun z => c * v z)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = supNorm (fun z => c * v z) := by field_simp

private lemma transition_entry_le_one {P : Matrix S S ℝ} (hP : IsTransitionMatrix P)
    (y x : S) : P y x ≤ 1 := by
  calc P y x ≤ ∑ x' : S, P y x' :=
        Finset.single_le_sum (fun x' _ => hP.1 y x') (Finset.mem_univ x)
    _ = 1 := hP.2 y

private lemma prod_measure_expect {N : ℕ} (F : Fin N → S → ℝ) :
    ∑ s' : Fin N → S, ∏ j, F j (s' j) = ∏ j, ∑ y, F j y := by
  classical
  calc ∑ s' : Fin N → S, ∏ j, F j (s' j)
      = ∑ s' ∈ Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset S)),
          ∏ j, F j (s' j) := by rw [Fintype.piFinset_univ]
    _ = ∏ j, ∑ y, F j y := (Finset.prod_univ_sum _ _).symm

/-- The explicit mean-field map is Lipschitz in the sup norm, with a constant depending
only on `|S|`. -/
private lemma meanFieldMap_lipschitz
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β : ℝ) (m m' : S → ℝ) :
    supNorm (fun x => meanFieldMap P0 P1 ν β m x - meanFieldMap P0 P1 ν β m' x)
      ≤ 3 * (Fintype.card S : ℝ)^2 * supNorm (fun y => m y - m' y) := by
  classical
  set D := supNorm (fun y => m y - m' y) with hD
  have hD0 : 0 ≤ D := supNorm_nonneg _
  have habsD : ∀ y, |m y - m' y| ≤ D := by
    intro y
    rw [hD]
    exact abs_le_supNorm (fun z => m z - m' z) y
  refine supNorm_le (by positivity) fun x => ?_
  have hcard1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨x⟩
  -- the activated fractions are |S|·D-close
  have hz : ∀ y : S, |activateFraction ν β m y - activateFraction ν β m' y|
      ≤ (Fintype.card S : ℝ) * D := by
    intro y
    have hH : |higherPriorityMass ν m y - higherPriorityMass ν m' y|
        ≤ ((Fintype.card S : ℝ) - 1) * D := by
      unfold higherPriorityMass
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hsub : (Finset.univ.filter fun v => ν y < ν v) ⊆ Finset.univ.erase y := by
        intro v hv
        rcases Finset.mem_filter.mp hv with ⟨-, hlt⟩
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ v⟩
        rintro rfl
        exact lt_irrefl _ hlt
      have hcardle : (((Finset.univ.filter fun v => ν y < ν v).card : ℕ) : ℝ)
          ≤ (Fintype.card S : ℝ) - 1 := by
        have h1 : (Finset.univ.filter fun v => ν y < ν v).card
            ≤ (Finset.univ.erase y).card := Finset.card_le_card hsub
        have h2 : (Finset.univ.erase y).card = Fintype.card S - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ]
        have hc1 : 1 ≤ Fintype.card S := Fintype.card_pos_iff.mpr ⟨x⟩
        have h3 : (Finset.univ.filter fun v => ν y < ν v).card ≤ Fintype.card S - 1 := by
          omega
        have h4 : ((Fintype.card S - 1 : ℕ) : ℝ) = (Fintype.card S : ℝ) - 1 := by
          rw [Nat.cast_sub hc1]; norm_num
        calc (((Finset.univ.filter fun v => ν y < ν v).card : ℕ) : ℝ)
            ≤ ((Fintype.card S - 1 : ℕ) : ℝ) := by exact_mod_cast h3
          _ = (Fintype.card S : ℝ) - 1 := h4
      calc ∑ v ∈ Finset.univ.filter fun v => ν y < ν v, |m v - m' v|
          ≤ ∑ _v ∈ Finset.univ.filter fun v => ν y < ν v, D :=
            Finset.sum_le_sum fun v _ => habsD v
        _ = (((Finset.univ.filter fun v => ν y < ν v).card : ℕ) : ℝ) * D := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((Fintype.card S : ℝ) - 1) * D := mul_le_mul_of_nonneg_right hcardle hD0
    unfold activateFraction
    refine le_trans (min_lipschitz _ _ _ _) ?_
    refine max_le (le_trans (habsD y) (by nlinarith)) ?_
    refine le_trans (max_zero_lipschitz _ _) ?_
    have heq : β - higherPriorityMass ν m y - (β - higherPriorityMass ν m' y)
        = -(higherPriorityMass ν m y - higherPriorityMass ν m' y) := by ring
    rw [heq, abs_neg]
    nlinarith [hH]
  -- per-coordinate estimate
  unfold meanFieldMap
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y : S,
      |(m y - activateFraction ν β m y) * P0 y x + activateFraction ν β m y * P1 y x
        - ((m' y - activateFraction ν β m' y) * P0 y x
            + activateFraction ν β m' y * P1 y x)|
      ≤ D + 2 * ((Fintype.card S : ℝ) * D) := by
    intro y
    have h01 : 0 ≤ P0 y x := hP0.1 y x
    have h02 : P0 y x ≤ 1 := transition_entry_le_one hP0 y x
    have h11 : 0 ≤ P1 y x := hP1.1 y x
    have h12 : P1 y x ≤ 1 := transition_entry_le_one hP1 y x
    have hrw : (m y - activateFraction ν β m y) * P0 y x
        + activateFraction ν β m y * P1 y x
        - ((m' y - activateFraction ν β m' y) * P0 y x
            + activateFraction ν β m' y * P1 y x)
        = (m y - m' y) * P0 y x
          + (activateFraction ν β m y - activateFraction ν β m' y) * (P1 y x - P0 y x) := by
      ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    have h1 : |(m y - m' y) * P0 y x| ≤ D := by
      rw [abs_mul, abs_of_nonneg h01]
      calc |m y - m' y| * P0 y x ≤ D * 1 :=
            mul_le_mul (habsD y) h02 h01 hD0
        _ = D := mul_one D
    have h2 : |(activateFraction ν β m y - activateFraction ν β m' y) * (P1 y x - P0 y x)|
        ≤ (Fintype.card S : ℝ) * D * 2 := by
      rw [abs_mul]
      have hb : |P1 y x - P0 y x| ≤ 2 := by
        rw [abs_le]
        constructor <;> nlinarith
      calc |activateFraction ν β m y - activateFraction ν β m' y| * |P1 y x - P0 y x|
          ≤ ((Fintype.card S : ℝ) * D) * 2 := by
            refine mul_le_mul (hz y) hb (abs_nonneg _) ?_
            positivity
      _ = (Fintype.card S : ℝ) * D * 2 := rfl
    linarith
  calc ∑ y : S,
        |(m y - activateFraction ν β m y) * P0 y x + activateFraction ν β m y * P1 y x
          - ((m' y - activateFraction ν β m' y) * P0 y x
              + activateFraction ν β m' y * P1 y x)|
      ≤ ∑ _y : S, (D + 2 * ((Fintype.card S : ℝ) * D)) :=
        Finset.sum_le_sum fun y _ => hterm y
    _ = (Fintype.card S : ℝ) * (D + 2 * ((Fintype.card S : ℝ) * D)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 3 * (Fintype.card S : ℝ)^2 * D := by
        have hcc : (Fintype.card S : ℝ) ≤ (Fintype.card S : ℝ)^2 := by nlinarith [hcard1]
        nlinarith [mul_le_mul_of_nonneg_right hcc hD0]

/-! ### Union bounds and the sub-Gaussian one-sided Chernoff bound -/

private lemma meanFieldMap_nonneg' (P0 P1 : Matrix S S ℝ)
    (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (hm : ∀ z, 0 ≤ m z) (z : S) :
    0 ≤ meanFieldMap P0 P1 ν β m z := by
  unfold meanFieldMap
  refine Finset.sum_nonneg fun y _ => ?_
  have h1 : 0 ≤ activateFraction ν β m y := by
    unfold activateFraction
    exact le_min (hm y) (le_max_left _ _)
  have h2 : activateFraction ν β m y ≤ m y := by
    unfold activateFraction
    exact min_le_left _ _
  have h3 := hP0.1 y z
  have h4 := hP1.1 y z
  nlinarith

private lemma meanFieldMap_mass' (P0 P1 : Matrix S S ℝ)
    (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (hm1 : ∑ z, m z = 1) :
    ∑ z, meanFieldMap P0 P1 ν β m z = 1 := by
  unfold meanFieldMap
  rw [Finset.sum_comm]
  have hrow : ∀ y : S,
      ∑ z : S, ((m y - activateFraction ν β m y) * P0 y z
          + activateFraction ν β m y * P1 y z) = m y := by
    intro y
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hP0.2 y, hP1.2 y]
    ring
  rw [Finset.sum_congr rfl fun y _ => hrow y]
  exact hm1

private lemma meanFieldIterate_isConfiguration (P0 P1 : Matrix S S ℝ)
    (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β : ℝ) (m : S → ℝ) (hm : IsConfiguration m) :
    ∀ t : ℕ, IsConfiguration (meanFieldIterate (meanFieldMap P0 P1 ν β) t m) := by
  intro t
  induction t with
  | zero => exact hm
  | succ t ih =>
    have hstep : meanFieldIterate (meanFieldMap P0 P1 ν β) (t + 1) m
        = meanFieldMap P0 P1 ν β (meanFieldIterate (meanFieldMap P0 P1 ν β) t m) := rfl
    rw [hstep]
    exact ⟨fun z => meanFieldMap_nonneg' P0 P1 hP0 hP1 ν β _ ih.1 z,
      meanFieldMap_mass' P0 P1 hP0 hP1 ν β _ ih.2⟩

/-! ### The interior ball around the fixed point lies in its priority region -/

private lemma vecMul_apply (v : S → ℝ) (K : Matrix S S ℝ) (z : S) :
    Matrix.vecMul v K z = ∑ y, v y * K y z := by
  simp [Matrix.vecMul, dotProduct]

private lemma vecMul_smul' (c : ℝ) (v : S → ℝ) (K : Matrix S S ℝ) (z : S) :
    Matrix.vecMul (fun y => c * v y) K z = c * Matrix.vecMul v K z := by
  rw [vecMul_apply, vecMul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma vecMul_sub' (u v : S → ℝ) (K : Matrix S S ℝ) (z : S) :
    Matrix.vecMul (fun y => u y - v y) K z
      = Matrix.vecMul u K z - Matrix.vecMul v K z := by
  rw [vecMul_apply, vecMul_apply, vecMul_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

private lemma vecMul_norm_le (K : Matrix S S ℝ) (v : S → ℝ) :
    supNorm (Matrix.vecMul v K)
      ≤ ((∑ y, ∑ z, |K y z|) + 1) * supNorm v := by
  classical
  have hB0 : (0:ℝ) ≤ (∑ y, ∑ z, |K y z|) + 1 := by positivity
  refine supNorm_le (mul_nonneg hB0 (supNorm_nonneg v)) fun z => ?_
  rw [vecMul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ y, |v y * K y z|
      = ∑ y, |v y| * |K y z| := Finset.sum_congr rfl fun y _ => abs_mul _ _
    _ ≤ ∑ y, supNorm v * |K y z| :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_right (abs_le_supNorm v y) (abs_nonneg _)
    _ = supNorm v * ∑ y, |K y z| := by rw [Finset.mul_sum]
    _ ≤ supNorm v * ((∑ y, ∑ z', |K y z'|) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (supNorm_nonneg v)
        have h1 : ∑ y, |K y z| ≤ ∑ y, ∑ z', |K y z'| := by
          refine Finset.sum_le_sum fun y _ => ?_
          exact Finset.single_le_sum (f := fun z' => |K y z'|)
            (fun z' _ => abs_nonneg _) (Finset.mem_univ z)
        linarith
    _ = ((∑ y, ∑ z', |K y z'|) + 1) * supNorm v := mul_comm _ _

private lemma vecMul_pow_norm_le (K : Matrix S S ℝ) (v : S → ℝ) (t : ℕ) :
    supNorm (Matrix.vecMul v (K ^ t))
      ≤ ((∑ y, ∑ z, |K y z|) + 1) ^ t * supNorm v := by
  induction t with
  | zero =>
    rw [pow_zero, Matrix.vecMul_one, pow_zero, one_mul]
  | succ t ih =>
    have hB0 : (0:ℝ) ≤ (∑ y, ∑ z, |K y z|) + 1 := by positivity
    have hstep : Matrix.vecMul v (K ^ (t + 1))
        = Matrix.vecMul (Matrix.vecMul v (K ^ t)) K := by
      rw [pow_succ, ← Matrix.vecMul_vecMul]
    rw [hstep]
    calc supNorm (Matrix.vecMul (Matrix.vecMul v (K ^ t)) K)
        ≤ ((∑ y, ∑ z, |K y z|) + 1) * supNorm (Matrix.vecMul v (K ^ t)) :=
          vecMul_norm_le K _
      _ ≤ ((∑ y, ∑ z, |K y z|) + 1)
            * (((∑ y, ∑ z, |K y z|) + 1) ^ t * supNorm v) :=
          mul_le_mul_of_nonneg_left ih hB0
      _ = ((∑ y, ∑ z, |K y z|) + 1) ^ (t + 1) * supNorm v := by
          rw [pow_succ]
          ring

/-! ### Linearity of `vecMul` in the vector, and scaling of the sup norm -/

private lemma higherPriorityMass_diff_le (ν : S → ℝ) (m m' : S → ℝ) (x : S) :
    |higherPriorityMass ν m x - higherPriorityMass ν m' x|
      ≤ (Fintype.card S : ℝ) * supNorm (fun y => m y - m' y) := by
  classical
  unfold higherPriorityMass
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ v ∈ Finset.univ.filter fun v => ν x < ν v, |m v - m' v|
      ≤ ∑ _v ∈ Finset.univ.filter fun v => ν x < ν v,
          supNorm (fun y => m y - m' y) :=
        Finset.sum_le_sum fun v _ => abs_le_supNorm (fun y => m y - m' y) v
    _ = (((Finset.univ.filter fun v => ν x < ν v).card : ℕ) : ℝ)
          * supNorm (fun y => m y - m' y) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card S : ℝ) * supNorm (fun y => m y - m' y) := by
        refine mul_le_mul_of_nonneg_right ?_ (supNorm_nonneg _)
        exact_mod_cast Finset.card_le_card (Finset.subset_univ _)

private lemma ball_in_region (ν : S → ℝ) (α : ℝ) (mstar : S → ℝ) (x : S)
    (hx1 : 0 < α - higherPriorityMass ν mstar x)
    (hx2 : α - higherPriorityMass ν mstar x < mstar x)
    (η : ℝ)
    (hη1 : (Fintype.card S : ℝ) * η < α - higherPriorityMass ν mstar x)
    (hη2 : ((Fintype.card S : ℝ) + 1) * η
      < higherPriorityMass ν mstar x + mstar x - α)
    (m : S → ℝ) (hball : supNorm (fun y => m y - mstar y) ≤ η) :
    IsPriorityRegion ν α m x := by
  have hH := higherPriorityMass_diff_le ν m mstar x
  have hcard0 : (0:ℝ) ≤ (Fintype.card S : ℝ) := Nat.cast_nonneg _
  have hHball : |higherPriorityMass ν m x - higherPriorityMass ν mstar x|
      ≤ (Fintype.card S : ℝ) * η := by
    refine le_trans hH (mul_le_mul_of_nonneg_left hball hcard0)
  have hmx : |m x - mstar x| ≤ η :=
    le_trans (abs_le_supNorm (fun y => m y - mstar y) x) hball
  have h1 := abs_le.mp hHball
  have h2 := abs_le.mp hmx
  constructor
  · linarith [h1.2]
  · linarith [h1.1, h2.1]

/-! ### The affine identity near the fixed point, in `vecMul` form -/

private lemma affine_diff (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (α : ℝ)
    (mstar : S → ℝ) (hmstar0 : ∀ z, 0 ≤ mstar z)
    (hfix : meanFieldMap P0 P1 ν α mstar = mstar)
    (x : S) (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z)
    (hregstar : IsPriorityRegion ν α mstar x)
    (m : S → ℝ) (hm0 : ∀ z, 0 ≤ m z) (hreg : IsPriorityRegion ν α m x) (z : S) :
    meanFieldMap P0 P1 ν α m z - mstar z
      = Matrix.vecMul (fun y => m y - mstar y) K z := by
  have h1 := hK m hm0 hreg
  have h2 := hK mstar hmstar0 hregstar
  have h3 : meanFieldMap P0 P1 ν α m z = (∑ y, m y * K y z) + b z := by
    rw [h1]
  have h4 : mstar z = (∑ y, mstar y * K y z) + b z := by
    conv_lhs => rw [← hfix]
    rw [h2]
  rw [vecMul_apply, h3, h4]
  rw [show ∑ y, (m y - mstar y) * K y z
    = (∑ y, m y * K y z) - ∑ y, mstar y * K y z by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring]
  ring

/-! ### Operator-norm bound and iteration for `vecMul` -/

private lemma configuration_sum {N : ℕ} (hN : 0 < N) (s : Fin N → S) :
    ∑ x : S, configuration s x = 1 := by
  classical
  have hcount : ∑ x : S, stateCount s x = N := by
    unfold stateCount
    rw [← Finset.card_eq_sum_card_fiberwise (f := s) (fun i _ => Finset.mem_univ (s i))]
    simp
  have hN' : ((N : ℝ)) ≠ 0 := by exact_mod_cast hN.ne'
  unfold configuration
  rw [← Finset.sum_div]
  rw [show ∑ x : S, (stateCount s x : ℝ) = ((∑ x : S, stateCount s x : ℕ) : ℝ) by
    rw [Nat.cast_sum], hcount]
  field_simp

private lemma rmabStep_nonneg {N : ℕ}
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (s s' : Fin N → S) : 0 ≤ rmabStep P0 P1 π s s' := by
  refine Finset.sum_nonneg fun a _ => mul_nonneg (hπJ.1 s a) ?_
  refine Finset.prod_nonneg fun j _ => ?_
  cases hb : a j <;> simp [rmabKernel, hb, hP0.1 (s j) (s' j), hP1.1 (s j) (s' j)]

private lemma rmabStep_total {N : ℕ}
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (s : Fin N → S) : ∑ s' : Fin N → S, rmabStep P0 P1 π s s' = 1 := by
  unfold rmabStep
  rw [Finset.sum_comm]
  have hinner : ∀ a : Fin N → Bool,
      ∑ s' : Fin N → S, π s a * ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)
        = π s a := by
    intro a
    rw [← Finset.mul_sum]
    rw [prod_measure_expect fun j y => rmabKernel P0 P1 (s j) (a j) y]
    have hone : ∀ j : Fin N, ∑ y, rmabKernel P0 P1 (s j) (a j) y = 1 := by
      intro j
      cases hb : a j <;> simp [rmabKernel, hb, hP0.2 (s j), hP1.2 (s j)]
    rw [Finset.prod_congr rfl fun j _ => hone j, Finset.prod_const_one, mul_one]
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  exact hπJ.2 s

private lemma rmabLaw_nonneg {N : ℕ}
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (s0 : Fin N → S) : ∀ (t : ℕ) (s : Fin N → S), 0 ≤ rmabLaw P0 P1 π s0 t s := by
  intro t
  induction t with
  | zero =>
    intro s
    simp only [rmabLaw]
    by_cases h : s = s0 <;> simp [h]
  | succ t ih =>
    intro s'
    simp only [rmabLaw]
    exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (ih s) (rmabStep_nonneg P0 P1 hP0 hP1 π hπJ s s')

private lemma rmabLaw_total {N : ℕ}
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (s0 : Fin N → S) : ∀ t : ℕ, ∑ s : Fin N → S, rmabLaw P0 P1 π s0 t s = 1 := by
  intro t
  induction t with
  | zero =>
    simp only [rmabLaw]
    rw [Finset.sum_ite_eq' Finset.univ s0 fun _ => (1:ℝ)]
    simp
  | succ t ih =>
    simp only [rmabLaw]
    rw [Finset.sum_comm]
    have hrow : ∀ s : Fin N → S,
        ∑ s' : Fin N → S, rmabLaw P0 P1 π s0 t s * rmabStep P0 P1 π s s'
          = rmabLaw P0 P1 π s0 t s := by
      intro s
      rw [← Finset.mul_sum, rmabStep_total P0 P1 hP0 hP1 π hπJ s, mul_one]
    rw [Finset.sum_congr rfl fun s _ => hrow s]
    exact ih


/-! ### Small new pieces -/

private lemma supNorm_le_l1Norm (v : S → ℝ) : supNorm v ≤ l1Norm v := by
  have h0 : (0:ℝ) ≤ l1Norm v := by
    unfold l1Norm
    positivity
  refine supNorm_le h0 fun x => ?_
  unfold l1Norm
  exact Finset.single_le_sum (f := fun z => |v z|) (fun z _ => abs_nonneg _)
    (Finset.mem_univ x)

private lemma activateFraction_fraction_lipschitz (ν : S → ℝ) (β α' : ℝ)
    (m : S → ℝ) (y : S) :
    |activateFraction ν β m y - activateFraction ν α' m y| ≤ |β - α'| := by
  unfold activateFraction
  refine le_trans (min_lipschitz _ _ _ _) ?_
  refine max_le ?_ ?_
  · rw [sub_self, abs_zero]
    exact abs_nonneg _
  · refine le_trans (max_zero_lipschitz _ _) ?_
    rw [show β - higherPriorityMass ν m y - (α' - higherPriorityMass ν m y)
      = β - α' by ring]

private lemma meanFieldMap_fraction_drift
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β α' : ℝ) (m : S → ℝ) :
    supNorm (fun x => meanFieldMap P0 P1 ν β m x - meanFieldMap P0 P1 ν α' m x)
      ≤ 2 * (Fintype.card S : ℝ) * |β - α'| := by
  refine supNorm_le (by positivity) fun x => ?_
  unfold meanFieldMap
  rw [← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ y : S,
      |(m y - activateFraction ν β m y) * P0 y x + activateFraction ν β m y * P1 y x
        - ((m y - activateFraction ν α' m y) * P0 y x
            + activateFraction ν α' m y * P1 y x)|
      ≤ 2 * |β - α'| := by
    intro y
    rw [show (m y - activateFraction ν β m y) * P0 y x
          + activateFraction ν β m y * P1 y x
        - ((m y - activateFraction ν α' m y) * P0 y x
            + activateFraction ν α' m y * P1 y x)
      = (activateFraction ν β m y - activateFraction ν α' m y) * (P1 y x - P0 y x)
      by ring]
    rw [abs_mul]
    have h1 := activateFraction_fraction_lipschitz ν β α' m y
    have h2 : |P1 y x - P0 y x| ≤ 2 := by
      have h3 := hP0.1 y x
      have h4 := transition_entry_le_one hP0 y x
      have h5 := hP1.1 y x
      have h6 := transition_entry_le_one hP1 y x
      rw [abs_le]
      constructor <;> linarith
    calc |activateFraction ν β m y - activateFraction ν α' m y| * |P1 y x - P0 y x|
        ≤ |β - α'| * 2 := mul_le_mul h1 h2 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |β - α'| := mul_comm _ _
  calc ∑ y : S,
      |(m y - activateFraction ν β m y) * P0 y x + activateFraction ν β m y * P1 y x
        - ((m y - activateFraction ν α' m y) * P0 y x
            + activateFraction ν α' m y * P1 y x)|
      ≤ ∑ _y : S, 2 * |β - α'| := Finset.sum_le_sum fun y _ => hterm y
    _ = (Fintype.card S : ℝ) * (2 * |β - α'|) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 2 * (Fintype.card S : ℝ) * |β - α'| := by ring

private lemma floor_fraction_close (α : ℝ) (hα : 0 ≤ α) {N : ℕ} (hN : 0 < N) :
    |(⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ) - α| ≤ 1 / (N : ℝ) := by
  have hN' : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h1 : (⌊α * (N : ℝ)⌋₊ : ℝ) ≤ α * (N : ℝ) := Nat.floor_le (by positivity)
  have h2 : α * (N : ℝ) - 1 < (⌊α * (N : ℝ)⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (α * (N : ℝ))
    linarith
  have h3 : (⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ) * (N : ℝ) = (⌊α * (N : ℝ)⌋₊ : ℝ) := by
    field_simp
  have h4 : 1 / (N : ℝ) * (N : ℝ) = 1 := by field_simp
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-! ### Stationarity: pushforward, product form, and the shifted law -/

private lemma occupancy_pushforward
    {N : ℕ} {St Act : Fin N → Type*}
    [∀ i, Fintype (St i)] [∀ i, DecidableEq (St i)]
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (π : JointState St → JointAction Act → ℝ) (hπJ : IsJointPolicy π)
    (μ : Joint (StateAction St Act) → ℝ)
    (hstat : IsStationary (inducedTransition P π) μ)
    (s' : JointState St) :
    occupancyStateMarginal μ s'
      = ∑ p, μ p * P (fun j => (p j).1) (fun j => (p j).2) s' := by
  classical
  set T := inducedTransition P π with hT
  set sp : Joint (StateAction St Act) → JointState St := fun p j => (p j).1 with hsp
  set ap : Joint (StateAction St Act) → JointAction Act := fun p j => (p j).2 with hap
  show occupancyStateMarginal μ s' = ∑ p, μ p * P (sp p) (ap p) s'
  rw [occupancyStateMarginal]
  calc ∑ q : Joint (StateAction St Act), (if (fun j => (q j).1) = s' then μ q else 0)
      = ∑ q : Joint (StateAction St Act),
          (if (fun j => (q j).1) = s' then (∑ p, μ p * T p q) else 0) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases h1 : (fun j => (q j).1) = s'
        · rw [if_pos h1, if_pos h1, hstat q]
        · rw [if_neg h1, if_neg h1]
    _ = ∑ q : Joint (StateAction St Act), ∑ p,
          (if (fun j => (q j).1) = s' then μ p * T p q else 0) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
    _ = ∑ p, ∑ q : Joint (StateAction St Act),
          (if (fun j => (q j).1) = s' then μ p * T p q else 0) := Finset.sum_comm
    _ = ∑ p, μ p * P (sp p) (ap p) s' := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        have hin : ∑ q : Joint (StateAction St Act),
            (if (fun j => (q j).1) = s' then T p q else 0)
              = P (sp p) (ap p) s' := by
          rw [← Equiv.sum_comp (splitStateAction (St := St) (Act := Act)).symm]
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_eq_single s']
          · have hτ : ∑ a' : JointAction Act, T p ((splitStateAction).symm (s', a'))
                = P (sp p) (ap p) s' * ∑ a' : JointAction Act, π s' a' := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun a' _ => ?_)
              rw [hT, inducedTransition]
              rfl
            have hstrip : ∀ a' : JointAction Act,
                (if (fun j => (((splitStateAction (St := St) (Act := Act)).symm
                      (s', a')) j).1) = s'
                 then T p ((splitStateAction (St := St) (Act := Act)).symm (s', a'))
                 else 0)
                = T p ((splitStateAction (St := St) (Act := Act)).symm (s', a')) :=
              fun a' => if_pos rfl
            rw [Finset.sum_congr rfl (fun a' _ => hstrip a'), hτ, hπJ.2 s', mul_one]
          · intro b _ hb
            refine Finset.sum_eq_zero (fun a' _ => ?_)
            refine if_neg ?_
            simpa [splitStateAction] using hb
          · intro h
            exact absurd (Finset.mem_univ _) h
        calc ∑ q : Joint (StateAction St Act),
              (if (fun j => (q j).1) = s' then μ p * T p q else 0)
            = ∑ q : Joint (StateAction St Act),
                μ p * (if (fun j => (q j).1) = s' then T p q else 0) := by
              refine Finset.sum_congr rfl (fun q _ => ?_)
              by_cases h1 : (fun j => (q j).1) = s' <;> simp [h1]
          _ = μ p * P (sp p) (ap p) s' := by rw [← Finset.mul_sum, hin]

private lemma stationary_product
    {N : ℕ} {St Act : Fin N → Type*}
    [∀ i, Fintype (St i)] [∀ i, DecidableEq (St i)]
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (P : JointState St → JointAction Act → JointState St → ℝ)
    (π : JointState St → JointAction Act → ℝ) (hπJ : IsJointPolicy π)
    (μ : Joint (StateAction St Act) → ℝ)
    (hstat : IsStationary (inducedTransition P π) μ)
    (q : Joint (StateAction St Act)) :
    μ q = occupancyStateMarginal μ (fun j => (q j).1)
      * π (fun j => (q j).1) (fun j => (q j).2) := by
  classical
  have h1 := hstat q
  rw [← h1]
  have h2 : ∀ p, inducedTransition P π p q
      = P (fun j => (p j).1) (fun j => (p j).2) (fun j => (q j).1)
        * π (fun j => (q j).1) (fun j => (q j).2) := fun p => rfl
  rw [Finset.sum_congr rfl fun p _ => by rw [h2 p]]
  rw [show ∑ p, μ p * (P (fun j => (p j).1) (fun j => (p j).2) (fun j => (q j).1)
      * π (fun j => (q j).1) (fun j => (q j).2))
    = (∑ p, μ p * P (fun j => (p j).1) (fun j => (p j).2) (fun j => (q j).1))
      * π (fun j => (q j).1) (fun j => (q j).2) by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring]
  rw [← occupancy_pushforward P π hπJ μ hstat]

private lemma state_marginal_stationary {N : ℕ}
    (P0 P1 : Matrix S S ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ)
    (s' : Fin N → S) :
    ∑ s : Fin N → S, occupancyStateMarginal μ s * rmabStep P0 P1 π s s'
      = occupancyStateMarginal μ s' := by
  classical
  rw [occupancy_pushforward
    (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π hπJ μ hstat s']
  unfold rmabStep
  calc ∑ s : Fin N → S, occupancyStateMarginal μ s *
        ∑ a : Fin N → Bool, π s a * ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)
      = ∑ s : Fin N → S, ∑ a : Fin N → Bool,
          occupancyStateMarginal μ s * π s a
            * ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
          occupancyStateMarginal μ (fun j => (p j).1)
            * π (fun j => (p j).1) (fun j => (p j).2)
            * ∏ j, rmabKernel P0 P1 ((p j).1) ((p j).2) (s' j) := by
        rw [← Equiv.sum_comp
          (splitStateAction (St := fun _ : Fin N => S)
            (Act := fun _ : Fin N => Bool)).symm
          (fun p => occupancyStateMarginal μ (fun j => (p j).1)
            * π (fun j => (p j).1) (fun j => (p j).2)
            * ∏ j, rmabKernel P0 P1 ((p j).1) ((p j).2) (s' j))]
        rw [Fintype.sum_prod_type]
        rfl
    _ = ∑ p : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)),
          μ p * ∏ j, rmabKernel P0 P1 ((p j).1) ((p j).2) (s' j) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [stationary_product
          (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π hπJ μ hstat p]
    _ = ∑ p, μ p * (fun s a s'' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s'' j))
          (fun j => (p j).1) (fun j => (p j).2) s' := rfl

private lemma law_shift {N : ℕ}
    (P0 P1 : Matrix S S ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ) (hπJ : IsJointPolicy π)
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hstat : IsStationary (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ) :
    ∀ (T : ℕ) (s'' : Fin N → S),
      ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 * rmabLaw P0 P1 π s0 T s''
        = occupancyStateMarginal μ s'' := by
  intro T
  induction T with
  | zero =>
    intro s''
    simp only [rmabLaw]
    rw [Finset.sum_congr rfl fun s0 _ => by rw [mul_ite, mul_one, mul_zero]]
    rw [Finset.sum_ite_eq]
    simp
  | succ T ih =>
    intro s''
    simp only [rmabLaw]
    calc ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
          ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s * rmabStep P0 P1 π s s''
        = ∑ s0 : Fin N → S, ∑ s : Fin N → S,
            occupancyStateMarginal μ s0 * rmabLaw P0 P1 π s0 T s
              * rmabStep P0 P1 π s s'' := by
          refine Finset.sum_congr rfl fun s0 _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ s : Fin N → S, ∑ s0 : Fin N → S,
            occupancyStateMarginal μ s0 * rmabLaw P0 P1 π s0 T s
              * rmabStep P0 P1 π s s'' := Finset.sum_comm
      _ = ∑ s : Fin N → S, occupancyStateMarginal μ s * rmabStep P0 P1 π s s'' := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [← Finset.sum_mul, ih s]
      _ = occupancyStateMarginal μ s'' :=
          state_marginal_stationary P0 P1 π hπJ μ hstat s''

/-! ### The expectation cascade and the iterate drift -/

private lemma cascade {N : ℕ} (hN : 0 < N)
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (α : ℝ)
    (π : (Fin N → S) → (Fin N → Bool) → ℝ)
    (hπ : IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π) (s0 : Fin N → S) :
    ∀ T : ℕ,
    ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
        supNorm (fun x => configuration s x
          - meanFieldIterate
              (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
              (configuration s0) x)
      ≤ (∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u)
          * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
  intro T
  induction T with
  | zero =>
    simp only [rmabLaw]
    rw [Finset.sum_congr rfl fun s _ => by rw [ite_mul, one_mul, zero_mul]]
    rw [Finset.sum_ite_eq' Finset.univ s0
      (fun s => supNorm (fun x => configuration s x
        - meanFieldIterate
            (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) 0
            (configuration s0) x))]
    simp only [Finset.mem_univ, if_true]
    rw [show (fun x => configuration s0 x
        - meanFieldIterate
            (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) 0
            (configuration s0) x)
      = fun x => configuration s0 x - configuration s0 x from rfl]
    rw [supNorm_self_zero, Finset.range_zero, Finset.sum_empty, zero_mul]
  | succ T ih =>
    have hπJ := hπ.1
    have hlaw0 := rmabLaw_nonneg P0 P1 hP0 hP1 π hπJ s0
    have hL0 : (0:ℝ) ≤ 3 * (Fintype.card S : ℝ)^2 := by positivity
    have hsqrt0 : (0:ℝ) ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) :=
      Real.sqrt_nonneg _
    simp only [rmabLaw]
    have hswap : ∑ s' : Fin N → S,
        (∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s * rmabStep P0 P1 π s s') *
          supNorm (fun x => configuration s' x
            - meanFieldIterate
                (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                (configuration s0) x)
        = ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
            ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
              supNorm (fun x => configuration s' x
                - meanFieldIterate
                    (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                    (configuration s0) x) := by
      calc ∑ s' : Fin N → S,
          (∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s * rmabStep P0 P1 π s s') *
            supNorm (fun x => configuration s' x
              - meanFieldIterate
                  (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                  (configuration s0) x)
          = ∑ s' : Fin N → S, ∑ s : Fin N → S,
              rmabLaw P0 P1 π s0 T s * (rmabStep P0 P1 π s s' *
                supNorm (fun x => configuration s' x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                      (configuration s0) x)) := by
            refine Finset.sum_congr rfl fun s' _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = ∑ s : Fin N → S, ∑ s' : Fin N → S,
              rmabLaw P0 P1 π s0 T s * (rmabStep P0 P1 π s s' *
                supNorm (fun x => configuration s' x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                      (configuration s0) x)) := Finset.sum_comm
        _ = ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
              ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
                supNorm (fun x => configuration s' x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                      (configuration s0) x) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [Finset.mul_sum]
    rw [hswap]
    -- the per-start one-step bound
    have hper : ∀ s : Fin N → S,
        ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
          supNorm (fun x => configuration s' x
            - meanFieldIterate
                (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                (configuration s0) x)
        ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          + 3 * (Fintype.card S : ℝ)^2 *
              supNorm (fun x => configuration s x
                - meanFieldIterate
                    (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                    (configuration s0) x) := by
      intro s
      have htri : ∀ s' : Fin N → S,
          supNorm (fun x => configuration s' x
            - meanFieldIterate
                (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                (configuration s0) x)
          ≤ supNorm (fun x => configuration s' x
              - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                  (configuration s) x)
            + 3 * (Fintype.card S : ℝ)^2 *
                supNorm (fun x => configuration s x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                      (configuration s0) x) := by
        intro s'
        have h1 := supNorm_triangle
          (fun x => configuration s' x)
          (fun x => meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
            (configuration s) x)
          (fun x => meanFieldIterate
            (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
            (configuration s0) x)
        refine le_trans h1 ?_
        gcongr
        have h2 : (fun x =>
            meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
              (configuration s) x
            - meanFieldIterate
                (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                (configuration s0) x)
            = fun x =>
              meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                (configuration s) x
              - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                  (meanFieldIterate
                    (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                    (configuration s0)) x := rfl
        rw [h2]
        exact meanFieldMap_lipschitz P0 P1 hP0 hP1 ν _ _ _
      have hstep0 : ∀ s', 0 ≤ rmabStep P0 P1 π s s' :=
        fun s' => rmabStep_nonneg P0 P1 hP0 hP1 π hπJ s s'
      calc ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
            supNorm (fun x => configuration s' x
              - meanFieldIterate
                  (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                  (configuration s0) x)
          ≤ ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
              (supNorm (fun x => configuration s' x
                - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                    (configuration s) x)
              + 3 * (Fintype.card S : ℝ)^2 *
                  supNorm (fun x => configuration s x
                    - meanFieldIterate
                        (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                        (configuration s0) x)) := by
            refine Finset.sum_le_sum fun s' _ => ?_
            exact mul_le_mul_of_nonneg_left (htri s') (hstep0 s')
        _ = (∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
              supNorm (fun x => configuration s' x
                - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                    (configuration s) x))
            + 3 * (Fintype.card S : ℝ)^2 *
                supNorm (fun x => configuration s x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                      (configuration s0) x) := by
            rw [show ∀ (A : (Fin N → S) → ℝ) (c : ℝ),
                (∑ s' : Fin N → S, rmabStep P0 P1 π s s' * (A s' + c))
                = (∑ s' : Fin N → S, rmabStep P0 P1 π s s' * A s')
                  + (∑ s' : Fin N → S, rmabStep P0 P1 π s s') * c from
              fun A c => by
                rw [Finset.sum_mul, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl fun s' _ => by ring]
            rw [rmabStep_total P0 P1 hP0 hP1 π hπJ s, one_mul]
        _ ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
            + 3 * (Fintype.card S : ℝ)^2 *
                supNorm (fun x => configuration s x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                      (configuration s0) x) := by
            gcongr
            calc ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
                  supNorm (fun x => configuration s' x
                    - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                        (configuration s) x)
                ≤ ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
                    l1Norm (fun x => configuration s' x
                      - meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))
                          (configuration s) x) := by
                  refine Finset.sum_le_sum fun s' _ => ?_
                  exact mul_le_mul_of_nonneg_left (supNorm_le_l1Norm _) (hstep0 s')
              _ ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) :=
                  rmab_one_step_concentration P0 P1 hP0 hP1 ν α N hN π hπ s
    -- combine with the induction hypothesis
    have hlawtot := rmabLaw_total P0 P1 hP0 hP1 π hπJ s0 T
    calc ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
          ∑ s' : Fin N → S, rmabStep P0 P1 π s s' *
            supNorm (fun x => configuration s' x
              - meanFieldIterate
                  (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) (T + 1)
                  (configuration s0) x)
        ≤ ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
            (Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
              + 3 * (Fintype.card S : ℝ)^2 *
                  supNorm (fun x => configuration s x
                    - meanFieldIterate
                        (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                        (configuration s0) x)) := by
          refine Finset.sum_le_sum fun s _ => ?_
          exact mul_le_mul_of_nonneg_left (hper s) (hlaw0 T s)
      _ = Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          + 3 * (Fintype.card S : ℝ)^2 *
              ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s *
                supNorm (fun x => configuration s x
                  - meanFieldIterate
                      (meanFieldMap P0 P1 ν ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T
                      (configuration s0) x) := by
          rw [show ∀ (A : (Fin N → S) → ℝ) (c d : ℝ),
              (∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s * (c + d * A s))
              = (∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s) * c
                + d * ∑ s : Fin N → S, rmabLaw P0 P1 π s0 T s * A s from
            fun A c d => by
              rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun s _ => by ring]
          rw [hlawtot, one_mul]
      _ ≤ Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          + 3 * (Fintype.card S : ℝ)^2 *
              ((∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u)
                * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))) := by
          gcongr
      _ = (∑ u ∈ Finset.range (T + 1), (3 * (Fintype.card S : ℝ)^2)^u)
            * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ)) := by
          rw [Finset.sum_range_succ' (fun u => (3 * (Fintype.card S : ℝ)^2)^u) T]
          rw [show ∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^(u + 1)
            = 3 * (Fintype.card S : ℝ)^2
              * ∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun u _ => by rw [pow_succ']]
          rw [pow_zero]
          ring

private lemma iterate_drift {N : ℕ}
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (β α' : ℝ) (m : S → ℝ) :
    ∀ T : ℕ,
    supNorm (fun x => meanFieldIterate (meanFieldMap P0 P1 ν β) T m x
        - meanFieldIterate (meanFieldMap P0 P1 ν α') T m x)
      ≤ (∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u)
          * (2 * (Fintype.card S : ℝ) * |β - α'|) := by
  intro T
  induction T with
  | zero =>
    rw [show (fun x => meanFieldIterate (meanFieldMap P0 P1 ν β) 0 m x
        - meanFieldIterate (meanFieldMap P0 P1 ν α') 0 m x)
      = fun x => m x - m x from rfl]
    rw [supNorm_self_zero, Finset.range_zero, Finset.sum_empty, zero_mul]
  | succ T ih =>
    have hL0 : (0:ℝ) ≤ 3 * (Fintype.card S : ℝ)^2 := by positivity
    have h1 := supNorm_triangle
      (fun x => meanFieldIterate (meanFieldMap P0 P1 ν β) (T + 1) m x)
      (fun x => meanFieldMap P0 P1 ν β
        (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x)
      (fun x => meanFieldIterate (meanFieldMap P0 P1 ν α') (T + 1) m x)
    refine le_trans h1 ?_
    have h2 : supNorm (fun x =>
        meanFieldIterate (meanFieldMap P0 P1 ν β) (T + 1) m x
        - meanFieldMap P0 P1 ν β
            (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x)
        ≤ 3 * (Fintype.card S : ℝ)^2 *
            supNorm (fun x => meanFieldIterate (meanFieldMap P0 P1 ν β) T m x
              - meanFieldIterate (meanFieldMap P0 P1 ν α') T m x) := by
      have hr : (fun x =>
          meanFieldIterate (meanFieldMap P0 P1 ν β) (T + 1) m x
          - meanFieldMap P0 P1 ν β
              (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x)
          = fun x => meanFieldMap P0 P1 ν β
              (meanFieldIterate (meanFieldMap P0 P1 ν β) T m) x
            - meanFieldMap P0 P1 ν β
                (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x := rfl
      rw [hr]
      exact meanFieldMap_lipschitz P0 P1 hP0 hP1 ν β _ _
    have h3 : supNorm (fun x =>
        meanFieldMap P0 P1 ν β
          (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x
        - meanFieldIterate (meanFieldMap P0 P1 ν α') (T + 1) m x)
        ≤ 2 * (Fintype.card S : ℝ) * |β - α'| := by
      have hr : (fun x =>
          meanFieldMap P0 P1 ν β
            (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x
          - meanFieldIterate (meanFieldMap P0 P1 ν α') (T + 1) m x)
          = fun x => meanFieldMap P0 P1 ν β
              (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x
            - meanFieldMap P0 P1 ν α'
                (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x := rfl
      rw [hr]
      exact meanFieldMap_fraction_drift P0 P1 hP0 hP1 ν β α' _
    calc supNorm (fun x =>
          meanFieldIterate (meanFieldMap P0 P1 ν β) (T + 1) m x
          - meanFieldMap P0 P1 ν β
              (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x)
        + supNorm (fun x =>
            meanFieldMap P0 P1 ν β
              (meanFieldIterate (meanFieldMap P0 P1 ν α') T m) x
            - meanFieldIterate (meanFieldMap P0 P1 ν α') (T + 1) m x)
        ≤ 3 * (Fintype.card S : ℝ)^2 *
            ((∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u)
              * (2 * (Fintype.card S : ℝ) * |β - α'|))
          + 2 * (Fintype.card S : ℝ) * |β - α'| := by
          refine add_le_add (le_trans h2 (mul_le_mul_of_nonneg_left ih hL0)) h3
      _ = (∑ u ∈ Finset.range (T + 1), (3 * (Fintype.card S : ℝ)^2)^u)
            * (2 * (Fintype.card S : ℝ) * |β - α'|) := by
          rw [Finset.sum_range_succ' (fun u => (3 * (Fintype.card S : ℝ)^2)^u) T]
          rw [show ∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^(u + 1)
            = 3 * (Fintype.card S : ℝ)^2
              * ∑ u ∈ Finset.range T, (3 * (Fintype.card S : ℝ)^2)^u by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun u _ => by rw [pow_succ']]
          rw [pow_zero]
          ring

/-! ### Part 3a: occupancy expectations and crude configuration bounds -/

private lemma occ_nonneg {N : ℕ}
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hμ : IsDist μ) (s : Fin N → S) :
    0 ≤ occupancyStateMarginal μ s := by
  refine Finset.sum_nonneg fun p _ => ?_
  by_cases h : (fun i => (p i).1) = s <;> simp [h, hμ.1 p]

private lemma occ_total {N : ℕ}
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (hμ : IsDist μ) :
    ∑ s : Fin N → S, occupancyStateMarginal μ s = 1 := by
  unfold occupancyStateMarginal
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun p _ =>
    Finset.sum_ite_eq Finset.univ (fun i => (p i).1) (fun _ => μ p)]
  simpa using hμ.2

private lemma expect_state_marginal {N : ℕ}
    (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ)
    (g : (Fin N → S) → ℝ) :
    ∑ p, μ p * g (fun j => (p j).1)
      = ∑ s : Fin N → S, occupancyStateMarginal μ s * g s := by
  unfold occupancyStateMarginal
  symm
  calc ∑ s : Fin N → S,
        (∑ p, if (fun i => (p i).1) = s then μ p else 0) * g s
      = ∑ s : Fin N → S, ∑ p,
          (if (fun i => (p i).1) = s then μ p * g s else 0) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases h : (fun i => (p i).1) = s <;> simp [h]
    _ = ∑ p, ∑ s : Fin N → S,
          (if (fun i => (p i).1) = s then μ p * g s else 0) := Finset.sum_comm
    _ = ∑ p, μ p * g (fun j => (p j).1) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_ite_eq Finset.univ (fun i => (p i).1)
          (fun s => μ p * g s)]
        simp

private lemma configuration_isConfiguration {N : ℕ} (hN : 0 < N) (s : Fin N → S) :
    IsConfiguration (configuration s) := by
  refine ⟨fun x => ?_, configuration_sum hN s⟩
  unfold configuration
  positivity

private lemma config_coord_le_one {m : S → ℝ} (hm : IsConfiguration m) (x : S) :
    m x ≤ 1 := by
  calc m x ≤ ∑ y, m y :=
        Finset.single_le_sum (fun y _ => hm.1 y) (Finset.mem_univ x)
    _ = 1 := hm.2

private lemma config_diff_le_one {m m' : S → ℝ}
    (hm : IsConfiguration m) (hm' : IsConfiguration m') :
    supNorm (fun x => m x - m' x) ≤ 1 := by
  refine supNorm_le zero_le_one fun x => ?_
  rw [abs_le]
  constructor
  · have := config_coord_le_one hm' x
    have := hm.1 x
    linarith
  · have := config_coord_le_one hm x
    have := hm'.1 x
    linarith

/-! ### Part 3b: the transient affine orbit near the fixed point -/

private lemma region_star (ν : S → ℝ) (α : ℝ) (mstar : S → ℝ) (x : S)
    (hx2 : 0 < α - higherPriorityMass ν mstar x)
    (hx3 : α - higherPriorityMass ν mstar x < mstar x) :
    IsPriorityRegion ν α mstar x := by
  constructor <;> [linarith; linarith]

private lemma transient_orbit (P0 P1 : Matrix S S ℝ)
    (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (α : ℝ) (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hfix : meanFieldMap P0 P1 ν α mstar = mstar)
    (x : S)
    (hx2 : 0 < α - higherPriorityMass ν mstar x)
    (hx3 : α - higherPriorityMass ν mstar x < mstar x)
    (K : Matrix S S ℝ) (b : S → ℝ)
    (hK : ∀ m : S → ℝ, (∀ z, 0 ≤ m z) → IsPriorityRegion ν α m x →
      meanFieldMap P0 P1 ν α m = fun z => (∑ y, m y * K y z) + b z)
    (η : ℝ) (hη0 : 0 < η)
    (hη1 : (Fintype.card S : ℝ) * η < α - higherPriorityMass ν mstar x)
    (hη2 : ((Fintype.card S : ℝ) + 1) * η
      < higherPriorityMass ν mstar x + mstar x - α)
    (T₃ : ℕ)
    (m : S → ℝ) (hm : IsConfiguration m)
    (hball : supNorm (fun y => m y - mstar y)
      ≤ η / ((∑ y, ∑ z, |K y z|) + 1) ^ T₃) :
    ∀ t, t ≤ T₃ → ∀ z,
      meanFieldIterate (meanFieldMap P0 P1 ν α) t m z - mstar z
        = Matrix.vecMul (fun y => m y - mstar y) (K ^ t) z := by
  have hBop1 : (1:ℝ) ≤ (∑ y, ∑ z, |K y z|) + 1 :=
    le_add_of_nonneg_left (by positivity)
  have hBopT : (0:ℝ) < ((∑ y, ∑ z, |K y z|) + 1) ^ T₃ := by positivity
  intro t
  induction t with
  | zero =>
    intro _ z
    rw [pow_zero, Matrix.vecMul_one]
    rfl
  | succ t ih =>
    intro ht z
    have ht' : t ≤ T₃ := Nat.le_of_succ_le ht
    have hihz := ih ht'
    -- the `t`-th iterate is inside the `η`-ball
    have hfun : (fun y => meanFieldIterate (meanFieldMap P0 P1 ν α) t m y - mstar y)
        = Matrix.vecMul (fun y => m y - mstar y) (K ^ t) := funext fun y => hihz y
    have hnorm : supNorm (fun y =>
        meanFieldIterate (meanFieldMap P0 P1 ν α) t m y - mstar y) ≤ η := by
      rw [hfun]
      refine le_trans (vecMul_pow_norm_le K _ t) ?_
      calc ((∑ y, ∑ z, |K y z|) + 1) ^ t * supNorm (fun y => m y - mstar y)
          ≤ ((∑ y, ∑ z, |K y z|) + 1) ^ T₃
              * (η / ((∑ y, ∑ z, |K y z|) + 1) ^ T₃) := by
            refine mul_le_mul (pow_le_pow_right₀ hBop1 ht') hball
              (supNorm_nonneg _) (by positivity)
        _ = η := by field_simp
    have hreg : IsPriorityRegion ν α
        (meanFieldIterate (meanFieldMap P0 P1 ν α) t m) x :=
      ball_in_region ν α mstar x hx2 hx3 η hη1 hη2 _ hnorm
    have hcfg : IsConfiguration (meanFieldIterate (meanFieldMap P0 P1 ν α) t m) :=
      meanFieldIterate_isConfiguration P0 P1 hP0 hP1 ν α m hm t
    have hstep : meanFieldIterate (meanFieldMap P0 P1 ν α) (t + 1) m z - mstar z
        = Matrix.vecMul (fun y =>
            meanFieldIterate (meanFieldMap P0 P1 ν α) t m y - mstar y) K z :=
      affine_diff P0 P1 ν α mstar hmstar.1 hfix x K b hK
        (region_star ν α mstar x hx2 hx3) _ hcfg.1 hreg z
    rw [hstep, hfun, pow_succ, ← Matrix.vecMul_vecMul]

/-! ### Part 3c: Theorem 7 — the stationary bootstrap and the assembly -/

set_option maxHeartbeats 2000000 in
/-- **Theorem 7.**  Index policies are asymptotically separable: under the uniform global
attractor property and non-degeneracy, the Markov entanglement of every agent in the
`N`-agent restless bandit under an index policy, at any exchangeable stationary law, is
`O(1/√N)`, with a constant depending only on the model data.

The proof is a stationary bootstrap.  Lemma 8 (M3) reduces the entanglement to the expected
deviation `E` of the configuration from the fixed point.  Stationarity lets `E` be evaluated
after any horizon; after the halving horizon of the linearised dynamics (M6 + M2) the
deviation is at most the one-trajectory concentration error (M4, cascaded), the fraction
drift `⌊αN⌋/N ↦ α`, half the original deviation, and the mass outside the
transient-containment ball — and that mass, evaluated after the uniform-attraction horizon,
is exponentially small by the multi-step concentration bound (M5). -/
theorem solution
    (P0 P1 : Matrix S S ℝ) (hP0 : IsTransitionMatrix P0) (hP1 : IsTransitionMatrix P1)
    (ν : S → ℝ) (hν : Function.Injective ν) (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (mstar : S → ℝ) (hmstar : IsConfiguration mstar)
    (hUGAP : IsUniformGlobalAttractor (meanFieldMap P0 P1 ν α) mstar)
    (hnd : IsNonDegenerateMeanField ν α mstar) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N : ℕ), 0 < N →
        ∀ (π : (Fin N → S) → (Fin N → Bool) → ℝ),
          IsIndexPolicy ν ⌊α * (N : ℝ)⌋₊ π →
          ∀ (μ : Joint (StateAction (fun _ : Fin N => S) (fun _ : Fin N => Bool)) → ℝ),
            IsDist μ →
            IsExchangeableDist μ →
            IsStationary (inducedTransition
              (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π) μ →
            ∀ i : Fin N,
              entanglementN i μ (inducedTransition
                  (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
                ≤ C / Real.sqrt (N : ℝ) := by
  classical
  have hcard0 : (0:ℝ) ≤ (Fintype.card S : ℝ) := Nat.cast_nonneg _
  -- the non-degenerate state and the affine piece of the map at `α`
  obtain ⟨x, hx1, hx2, hx3⟩ := hnd
  obtain ⟨K, b, hK⟩ := (meanFieldMap_piecewise_affine P0 P1 ν hν α).2 x
  obtain ⟨hstab, hreach⟩ := rmab_local_stability P0 P1 hP0 hP1 ν hν α hα hα1
    mstar hmstar hUGAP x ⟨hx1, hx2, hx3⟩ K b hK
  obtain ⟨C₆, ρ, hC₆0, hρ0, hρ1, hstabv⟩ := hstab
  -- a horizon at which the tangent dynamics have contracted by half
  obtain ⟨T₃, hT₃⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < 1 / (2 * (C₆ + 1)) by positivity) hρ1
  have hhalf : C₆ * ρ ^ T₃ ≤ 1 / 2 := by
    have h1 : C₆ * ρ ^ T₃ ≤ (C₆ + 1) * ρ ^ T₃ :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hρ0 _)
    have h2 : (C₆ + 1) * ρ ^ T₃ ≤ (C₆ + 1) * (1 / (2 * (C₆ + 1))) :=
      mul_le_mul_of_nonneg_left hT₃.le (by linarith)
    have h3 : (C₆ + 1) * (1 / (2 * (C₆ + 1))) = 1 / 2 := by
      field_simp
    linarith
  -- the in-region radius `η` around the fixed point
  have hH2pos : 0 < higherPriorityMass ν mstar x + mstar x - α := by linarith
  obtain ⟨η, hη0, hη1, hη2⟩ : ∃ η : ℝ, 0 < η ∧
      (Fintype.card S : ℝ) * η < α - higherPriorityMass ν mstar x ∧
      ((Fintype.card S : ℝ) + 1) * η
        < higherPriorityMass ν mstar x + mstar x - α := by
    have key : ∀ d c M G : ℝ, 0 ≤ d → d < c → 0 < M → M ≤ G →
        d * (M / c) < G := by
      intro d c M G hd hdc hM hMG
      have hc : 0 < c := lt_of_le_of_lt hd hdc
      have h1 : d * (M / c) * c = d * M := by field_simp
      nlinarith [h1, mul_le_mul_of_nonneg_left hMG hd, mul_pos hM hc]
    have hmin0 : 0 < min (α - higherPriorityMass ν mstar x)
        (higherPriorityMass ν mstar x + mstar x - α) := lt_min hx2 hH2pos
    refine ⟨min (α - higherPriorityMass ν mstar x)
        (higherPriorityMass ν mstar x + mstar x - α)
        / ((Fintype.card S : ℝ) + 2),
      div_pos hmin0 (by positivity), ?_, ?_⟩
    · exact key _ _ _ _ hcard0 (by linarith) hmin0
        (min_le_left _ _)
    · exact key _ _ _ _ (by positivity) (by linarith) hmin0
        (min_le_right _ _)
  -- the transient-containment radius
  obtain ⟨r, hr0, hrdef⟩ : ∃ r : ℝ, 0 < r ∧
      r = η / ((∑ y, ∑ z, |K y z|) + 1) ^ T₃ :=
    ⟨_, div_pos hη0 (by positivity), rfl⟩
  -- the uniform approach horizon at radius `r/4`
  obtain ⟨Ttil, hTtil⟩ := hreach (r / 4) (by positivity)
  -- multi-step concentration and its per-run tolerance `δ*`
  obtain ⟨K₅, hK₅0, hM5⟩ := rmab_multi_step_concentration P0 P1 hP0 hP1 ν hν α hα hα1
  obtain ⟨δstar, hδ0, hδthresh⟩ : ∃ δ : ℝ, 0 < δ ∧
      (∑ j ∈ Finset.range (Ttil + 1), K₅ ^ j) * δ = r / 2 := by
    have hSig1 : (1:ℝ) ≤ ∑ j ∈ Finset.range (Ttil + 1), K₅ ^ j := by
      calc (1:ℝ) = K₅ ^ 0 := (pow_zero K₅).symm
        _ ≤ ∑ j ∈ Finset.range (Ttil + 1), K₅ ^ j :=
            Finset.single_le_sum (f := fun j => K₅ ^ j)
              (fun j _ => pow_nonneg hK₅0 j)
              (Finset.mem_range.mpr (Nat.succ_pos _))
    have hSig0 : (0:ℝ) < ∑ j ∈ Finset.range (Ttil + 1), K₅ ^ j := by linarith
    refine ⟨(r / 2) / ∑ j ∈ Finset.range (Ttil + 1), K₅ ^ j,
      div_pos (by linarith) hSig0, ?_⟩
    rw [mul_comm]
    exact div_mul_cancel₀ _ hSig0.ne'
  -- the size threshold beyond which the drift is dominated
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge
    (8 * (Fintype.card S : ℝ)
      * (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u) / r + 1)
  have hA₃0 : (0:ℝ)
      ≤ ∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u := by
    positivity
  have hAtil0 : (0:ℝ)
      ≤ ∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u := by
    positivity
  -- the constant of the theorem
  obtain ⟨C₁, hC₁0, hC₁def⟩ : ∃ C₁ : ℝ, 0 ≤ C₁ ∧
      C₁ = 2 * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * Real.sqrt (Fintype.card S : ℝ)
        + 4 * (Fintype.card S : ℝ)
              * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
        + 8 * (Ttil : ℝ) * (Fintype.card S : ℝ) / δstar ^ 2 := by
    refine ⟨_, ?_, rfl⟩
    have h1 : (0:ℝ)
        ≤ 2 * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
          * Real.sqrt (Fintype.card S : ℝ) :=
      mul_nonneg (by linarith) (Real.sqrt_nonneg _)
    have h2 : (0:ℝ) ≤ 4 * (Fintype.card S : ℝ)
        * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u) :=
      mul_nonneg (by positivity) hA₃0
    have h3 : (0:ℝ) ≤ 8 * (Ttil : ℝ) * (Fintype.card S : ℝ) / δstar ^ 2 :=
      div_nonneg (by positivity) (sq_nonneg _)
    linarith
  refine ⟨(Fintype.card S : ℝ) ^ 2 * (C₁ + Real.sqrt (N₀ : ℝ)),
    mul_nonneg (by positivity) (add_nonneg hC₁0 (Real.sqrt_nonneg _)), ?_⟩
  intro N hN π hπ μ hμ hexch hstat i
  have hπJ : IsJointPolicy π := hπ.1
  have hNr : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsqrtN : (0:ℝ) < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hN1r : (1:ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith [Real.sq_sqrt hNr.le, sq_nonneg (Real.sqrt (N : ℝ) - 1),
      Real.sqrt_nonneg (N : ℝ)]
  have hβclose := floor_fraction_close α hα.le hN
  -- the deviation expectation at stationarity, and the mass of the far event
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = ∑ s : Fin N → S, occupancyStateMarginal μ s
      * supNorm (fun z => configuration s z - mstar z) := ⟨_, rfl⟩
  obtain ⟨Pfar, hPdef⟩ : ∃ P : ℝ, P = ∑ s : Fin N → S, occupancyStateMarginal μ s
      * (if r < supNorm (fun z => configuration s z - mstar z)
          then (1:ℝ) else 0) := ⟨_, rfl⟩
  have hE1 : E ≤ 1 := by
    rw [hEdef]
    calc ∑ s : Fin N → S, occupancyStateMarginal μ s
          * supNorm (fun z => configuration s z - mstar z)
        ≤ ∑ s : Fin N → S, occupancyStateMarginal μ s * 1 :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
            (config_diff_le_one (configuration_isConfiguration hN s) hmstar)
            (occ_nonneg μ hμ s)
      _ = 1 := by
          rw [Finset.sum_congr rfl fun s _ =>
            mul_one (occupancyStateMarginal μ s), occ_total μ hμ]
  -- M3: entanglement is dominated by `|S|² E`
  have hM3 := rmab_entanglement_le_configuration_deviation P0 P1 hP0 hP1 ν hν
    α hα hα1 mstar hmstar N hN π hπ μ hμ hexch hstat i
  have hbridge : ∑ p, μ p
      * supNorm (fun z => configuration (fun j => (p j).1) z - mstar z) = E := by
    rw [hEdef]
    exact expect_state_marginal μ
      (fun s => supNorm (fun z => configuration s z - mstar z))
  have hM3' : entanglementN i μ (inducedTransition
      (fun s a s' => ∏ j, rmabKernel P0 P1 (s j) (a j) (s' j)) π)
      ≤ (Fintype.card S : ℝ) ^ 2 * E := by
    refine le_trans hM3 (le_of_eq ?_)
    rw [hbridge]
  -- the stationarity shift, generically in the weight
  have hshift : ∀ (T : ℕ) (f : (Fin N → S) → ℝ),
      ∑ s'' : Fin N → S, occupancyStateMarginal μ s'' * f s''
        = ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
            ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T s'' * f s'' := by
    intro T f
    calc ∑ s'' : Fin N → S, occupancyStateMarginal μ s'' * f s''
        = ∑ s'' : Fin N → S,
            (∑ s0 : Fin N → S, occupancyStateMarginal μ s0
              * rmabLaw P0 P1 π s0 T s'') * f s'' := by
          refine Finset.sum_congr rfl fun s'' _ => ?_
          rw [law_shift P0 P1 π hπJ μ hstat T s'']
      _ = ∑ s'' : Fin N → S, ∑ s0 : Fin N → S,
            occupancyStateMarginal μ s0 * rmabLaw P0 P1 π s0 T s'' * f s'' :=
          Finset.sum_congr rfl fun s'' _ => Finset.sum_mul _ _ _
      _ = ∑ s0 : Fin N → S, ∑ s'' : Fin N → S,
            occupancyStateMarginal μ s0 * rmabLaw P0 P1 π s0 T s'' * f s'' :=
          Finset.sum_comm
      _ = ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
            ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T s'' * f s'' := by
          refine Finset.sum_congr rfl fun s0 _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s'' _ => by ring
  -- pointwise: the `T₃`-iterate at `α` halves the deviation inside the ball
  have hcontr : ∀ s0 : Fin N → S,
      supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) T₃
          (configuration s0) z - mstar z)
        ≤ 1 / 2 * supNorm (fun z => configuration s0 z - mstar z)
          + (if r < supNorm (fun z => configuration s0 z - mstar z)
              then (1:ℝ) else 0) := by
    intro s0
    by_cases hfar : r < supNorm (fun z => configuration s0 z - mstar z)
    · rw [if_pos hfar]
      have h1 : supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) T₃
          (configuration s0) z - mstar z) ≤ 1 :=
        config_diff_le_one
          (meanFieldIterate_isConfiguration P0 P1 hP0 hP1 ν α _
            (configuration_isConfiguration hN s0) T₃) hmstar
      have h2 := supNorm_nonneg (fun z => configuration s0 z - mstar z)
      linarith
    · rw [if_neg hfar, add_zero]
      have hball : supNorm (fun y => configuration s0 y - mstar y)
          ≤ η / ((∑ y, ∑ z, |K y z|) + 1) ^ T₃ := by
        rw [← hrdef]
        exact not_lt.mp hfar
      have horbit := transient_orbit P0 P1 hP0 hP1 ν α mstar hmstar hUGAP.1 x
        hx2 hx3 K b hK η hη0 hη1 hη2 T₃ (configuration s0)
        (configuration_isConfiguration hN s0) hball T₃ le_rfl
      have hfun : (fun z => meanFieldIterate (meanFieldMap P0 P1 ν α) T₃
            (configuration s0) z - mstar z)
          = Matrix.vecMul (fun y => configuration s0 y - mstar y) (K ^ T₃) :=
        funext horbit
      rw [hfun]
      have htan : (∑ z, (configuration s0 z - mstar z)) = 0 := by
        rw [Finset.sum_sub_distrib, configuration_sum hN s0, hmstar.2, sub_self]
      refine le_trans (hstabv (fun y => configuration s0 y - mstar y) htan T₃) ?_
      exact mul_le_mul_of_nonneg_right hhalf (supNorm_nonneg _)
  -- the one-horizon inner bound: cascade + drift + contraction
  have hinner : ∀ s0 : Fin N → S,
      ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
          * supNorm (fun z => configuration s'' z - mstar z)
        ≤ (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          + ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
          + (1 / 2 * supNorm (fun z => configuration s0 z - mstar z)
          + (if r < supNorm (fun z => configuration s0 z - mstar z)
              then (1:ℝ) else 0))) := by
    intro s0
    have htri : ∀ s'' : Fin N → S,
        supNorm (fun z => configuration s'' z - mstar z)
          ≤ supNorm (fun z => configuration s'' z
              - meanFieldIterate (meanFieldMap P0 P1 ν
                  ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z)
            + supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
                  ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z
                - mstar z) :=
      fun s'' => supNorm_triangle _ _ _
    have hW : supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
          ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z - mstar z)
        ≤ (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
            * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
          + (1 / 2 * supNorm (fun z => configuration s0 z - mstar z)
          + (if r < supNorm (fun z => configuration s0 z - mstar z)
              then (1:ℝ) else 0)) := by
      refine le_trans (supNorm_triangle _
        (meanFieldIterate (meanFieldMap P0 P1 ν α) T₃ (configuration s0)) _) ?_
      refine add_le_add ?_ (hcontr s0)
      refine le_trans (iterate_drift (N := N) P0 P1 hP0 hP1 ν
        ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) α (configuration s0) T₃) ?_
      refine mul_le_mul_of_nonneg_left ?_ hA₃0
      exact mul_le_mul_of_nonneg_left hβclose (by positivity)
    calc ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
            * supNorm (fun z => configuration s'' z - mstar z)
        ≤ ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
            * (supNorm (fun z => configuration s'' z
                - meanFieldIterate (meanFieldMap P0 P1 ν
                    ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z)
              + supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
                    ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z
                  - mstar z)) :=
          Finset.sum_le_sum fun s'' _ => mul_le_mul_of_nonneg_left (htri s'')
            (rmabLaw_nonneg P0 P1 hP0 hP1 π hπJ s0 T₃ s'')
      _ = (∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
              * supNorm (fun z => configuration s'' z
                - meanFieldIterate (meanFieldMap P0 P1 ν
                    ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z))
            + (∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s'')
              * supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
                  ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) T₃ (configuration s0) z
                  - mstar z) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun s'' _ => by ring
      _ ≤ (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
            + ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
            + (1 / 2 * supNorm (fun z => configuration s0 z - mstar z)
            + (if r < supNorm (fun z => configuration s0 z - mstar z)
                then (1:ℝ) else 0))) := by
          refine add_le_add (cascade hN P0 P1 hP0 hP1 ν α π hπ s0 T₃) ?_
          rw [rmabLaw_total P0 P1 hP0 hP1 π hπJ s0 T₃, one_mul]
          exact hW
  -- the bootstrap inequality
  have hboot : E ≤ (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
        * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
      + ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
        * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
      + (1 / 2 * E + Pfar)) := by
    have hE2 : E = ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
        ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
          * supNorm (fun z => configuration s'' z - mstar z) := by
      rw [hEdef]
      exact hshift T₃ (fun s => supNorm (fun z => configuration s z - mstar z))
    conv_lhs => rw [hE2]
    calc ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
          ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 T₃ s''
            * supNorm (fun z => configuration s'' z - mstar z)
        ≤ ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
            ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
              + ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
              + (1 / 2 * supNorm (fun z => configuration s0 z - mstar z)
              + (if r < supNorm (fun z => configuration s0 z - mstar z)
                  then (1:ℝ) else 0)))) :=
          Finset.sum_le_sum fun s0 _ =>
            mul_le_mul_of_nonneg_left (hinner s0) (occ_nonneg μ hμ s0)
      _ = ∑ s0 : Fin N → S,
            (occupancyStateMarginal μ s0
                * ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                    * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
                  + (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                    * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ))))
              + (1 / 2 * (occupancyStateMarginal μ s0
                  * supNorm (fun z => configuration s0 z - mstar z))
              + occupancyStateMarginal μ s0
                  * (if r < supNorm (fun z => configuration s0 z - mstar z)
                      then (1:ℝ) else 0))) :=
          Finset.sum_congr rfl fun s0 _ => by ring
      _ = (∑ s0 : Fin N → S, occupancyStateMarginal μ s0)
            * ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
              + (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
                * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ))))
          + (1 / 2 * (∑ s0 : Fin N → S, occupancyStateMarginal μ s0
              * supNorm (fun z => configuration s0 z - mstar z))
          + ∑ s0 : Fin N → S, occupancyStateMarginal μ s0
              * (if r < supNorm (fun z => configuration s0 z - mstar z)
                  then (1:ℝ) else 0)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_mul, ← Finset.mul_sum]
      _ = (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
            * Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          + ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
            * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
          + (1 / 2 * E + Pfar)) := by
          rw [occ_total μ hμ, one_mul, ← hEdef, ← hPdef]
          ring
  -- both regimes give `E ≤ (C₁ + √N₀)/√N`
  have hEbound : E ≤ (C₁ + Real.sqrt (N₀ : ℝ)) / Real.sqrt (N : ℝ) := by
    by_cases hbig : N₀ ≤ N
    · -- large `N`: the far event is exponentially rare
      have hNge : ((N₀ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbig
      have hrN : 8 * (Fintype.card S : ℝ)
          * (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
          ≤ r * (N : ℝ) := by
        have h1 := le_trans hN₀ hNge
        have h2 : (8 * (Fintype.card S : ℝ)
            * (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u) / r) * r
            = 8 * (Fintype.card S : ℝ)
              * (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u) :=
          div_mul_cancel₀ _ hr0.ne'
        have h3 := mul_le_mul_of_nonneg_left h1 hr0.le
        nlinarith [hr0]
      have hdriftTil :
          (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
            * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ))) ≤ r / 4 := by
        rw [show (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
            = 2 * (Fintype.card S : ℝ)
              * (∑ u ∈ Finset.range Ttil, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              / (N : ℝ) from by ring]
        rw [div_le_iff₀ hNr]
        nlinarith [hrN]
      have hWtil : ∀ s0 : Fin N → S,
          supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
              ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) Ttil (configuration s0) z
              - mstar z) ≤ r / 2 := by
        intro s0
        refine le_trans (supNorm_triangle _
          (meanFieldIterate (meanFieldMap P0 P1 ν α) Ttil (configuration s0)) _) ?_
        have hd : supNorm (fun z => meanFieldIterate (meanFieldMap P0 P1 ν
            ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) Ttil (configuration s0) z
              - meanFieldIterate (meanFieldMap P0 P1 ν α) Ttil (configuration s0) z)
            ≤ r / 4 := by
          refine le_trans (le_trans (iterate_drift (N := N) P0 P1 hP0 hP1 ν
            ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ)) α (configuration s0) Ttil) ?_)
            hdriftTil
          refine mul_le_mul_of_nonneg_left ?_ hAtil0
          exact mul_le_mul_of_nonneg_left hβclose (by positivity)
        have hg := hTtil (configuration s0) (configuration_isConfiguration hN s0)
        linarith
      have hfarrow : ∀ s0 : Fin N → S,
          ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 Ttil s''
              * (if r < supNorm (fun z => configuration s'' z - mstar z)
                  then (1:ℝ) else 0)
            ≤ 2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
                * Real.exp (-(N : ℝ) * δstar ^ 2 / 2) := by
        intro s0
        have h5 := hM5 N hN π hπ s0 Ttil δstar hδ0
        have h1 : ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 Ttil s''
              * (if r < supNorm (fun z => configuration s'' z - mstar z)
                  then (1:ℝ) else 0)
            = ∑ s'' ∈ Finset.univ.filter (fun s'' : Fin N → S =>
                r < supNorm (fun z => configuration s'' z - mstar z)),
                rmabLaw P0 P1 π s0 Ttil s'' := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun s'' _ => ?_
          by_cases h : r < supNorm (fun z => configuration s'' z - mstar z)
          · simp [h]
          · simp [h]
        rw [h1]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun s'' _ _ => rmabLaw_nonneg P0 P1 hP0 hP1 π hπJ s0 Ttil s'')) h5
        intro s'' hs''
        rw [Finset.mem_filter] at hs'' ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hδthresh]
        have htri2 := supNorm_triangle (configuration s'')
          (meanFieldIterate (meanFieldMap P0 P1 ν
            ((⌊α * (N : ℝ)⌋₊ : ℝ) / (N : ℝ))) Ttil (configuration s0)) mstar
        have hw := hWtil s0
        have hfar := hs''.2
        linarith
      have hPfarB : Pfar ≤ 2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
          * Real.exp (-(N : ℝ) * δstar ^ 2 / 2) := by
        have hP2 : Pfar = ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
            ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 Ttil s''
              * (if r < supNorm (fun z => configuration s'' z - mstar z)
                  then (1:ℝ) else 0) := by
          rw [hPdef]
          exact hshift Ttil (fun s =>
            if r < supNorm (fun z => configuration s z - mstar z)
            then (1:ℝ) else 0)
        rw [hP2]
        calc ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
              ∑ s'' : Fin N → S, rmabLaw P0 P1 π s0 Ttil s''
                * (if r < supNorm (fun z => configuration s'' z - mstar z)
                    then (1:ℝ) else 0)
            ≤ ∑ s0 : Fin N → S, occupancyStateMarginal μ s0 *
                (2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
                  * Real.exp (-(N : ℝ) * δstar ^ 2 / 2)) :=
              Finset.sum_le_sum fun s0 _ =>
                mul_le_mul_of_nonneg_left (hfarrow s0) (occ_nonneg μ hμ s0)
          _ = 2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
                * Real.exp (-(N : ℝ) * δstar ^ 2 / 2) := by
              rw [← Finset.sum_mul, occ_total μ hμ, one_mul]
      -- the exponential is at most `(2/δ*²)/√N`
      have hexpB : Real.exp (-(N : ℝ) * δstar ^ 2 / 2)
          ≤ 2 / δstar ^ 2 * (1 / Real.sqrt (N : ℝ)) := by
        have harg : -(N : ℝ) * δstar ^ 2 / 2
            = -((N : ℝ) * δstar ^ 2 / 2) := by ring
        rw [harg]
        have h1z : (N : ℝ) * δstar ^ 2 / 2
            ≤ Real.exp ((N : ℝ) * δstar ^ 2 / 2) := by
          have := Real.add_one_le_exp ((N : ℝ) * δstar ^ 2 / 2)
          linarith
        have hez : Real.exp (-((N : ℝ) * δstar ^ 2 / 2))
            * ((N : ℝ) * δstar ^ 2 / 2) ≤ 1 := by
          calc Real.exp (-((N : ℝ) * δstar ^ 2 / 2))
                * ((N : ℝ) * δstar ^ 2 / 2)
              ≤ Real.exp (-((N : ℝ) * δstar ^ 2 / 2))
                * Real.exp ((N : ℝ) * δstar ^ 2 / 2) :=
                mul_le_mul_of_nonneg_left h1z (Real.exp_pos _).le
            _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        rw [div_mul_div_comm, mul_one, le_div_iff₀ (by positivity)]
        have h6 : Real.exp (-((N : ℝ) * δstar ^ 2 / 2))
            * (δstar ^ 2 * Real.sqrt (N : ℝ)) * (N : ℝ) ≤ 2 * (N : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_right hez
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (Real.sqrt_nonneg (N : ℝ))),
            hs, (Real.exp_pos (-((N : ℝ) * δstar ^ 2 / 2))).le, sq_nonneg δstar]
        exact le_of_mul_le_mul_right h6 hNr
      -- collect
      have hsqrtdiv : Real.sqrt ((Fintype.card S : ℝ) / (N : ℝ))
          = Real.sqrt (Fintype.card S : ℝ) * (1 / Real.sqrt (N : ℝ)) := by
        rw [Real.sqrt_div hcard0, div_eq_mul_one_div]
      have honeN : 1 / (N : ℝ) ≤ 1 / Real.sqrt (N : ℝ) := by
        rw [div_le_div_iff₀ hNr hsqrtN]
        linarith [hs]
      have hX₂ : (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
          * (2 * (Fintype.card S : ℝ) * (1 / (N : ℝ)))
          ≤ (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
            * (2 * (Fintype.card S : ℝ) * (1 / Real.sqrt (N : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hA₃0
        exact mul_le_mul_of_nonneg_left honeN (by positivity)
      have hPB2 : Pfar ≤ 2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
          * (2 / δstar ^ 2 * (1 / Real.sqrt (N : ℝ))) := by
        refine le_trans hPfarB ?_
        exact mul_le_mul_of_nonneg_left hexpB (by positivity)
      have hb := hboot
      rw [hsqrtdiv] at hb
      have hEhalf : E ≤ C₁ * (1 / Real.sqrt (N : ℝ)) := by
        rw [hC₁def, add_mul, add_mul]
        have e1 : 2 * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * Real.sqrt (Fintype.card S : ℝ) * (1 / Real.sqrt (N : ℝ))
            = 2 * ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (Real.sqrt (Fintype.card S : ℝ) * (1 / Real.sqrt (N : ℝ)))) := by
          ring
        have e2 : 4 * (Fintype.card S : ℝ)
              * (∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (1 / Real.sqrt (N : ℝ))
            = 2 * ((∑ u ∈ Finset.range T₃, (3 * (Fintype.card S : ℝ) ^ 2) ^ u)
              * (2 * (Fintype.card S : ℝ) * (1 / Real.sqrt (N : ℝ)))) := by
          ring
        have e3 : 8 * (Ttil : ℝ) * (Fintype.card S : ℝ) / δstar ^ 2
              * (1 / Real.sqrt (N : ℝ))
            = 2 * (2 * (Ttil : ℝ) * (Fintype.card S : ℝ)
              * (2 / δstar ^ 2 * (1 / Real.sqrt (N : ℝ)))) := by
          ring
        rw [e1, e2, e3]
        linarith [hb, hX₂, hPB2]
      calc E ≤ C₁ * (1 / Real.sqrt (N : ℝ)) := hEhalf
        _ = C₁ / Real.sqrt (N : ℝ) := by rw [mul_one_div]
        _ ≤ (C₁ + Real.sqrt (N₀ : ℝ)) / Real.sqrt (N : ℝ) := by
            rw [add_div]
            have h0 : 0 ≤ Real.sqrt ((N₀ : ℕ) : ℝ) / Real.sqrt (N : ℝ) :=
              div_nonneg (Real.sqrt_nonneg _) hsqrtN.le
            linarith
    · -- small `N`: the crude bound
      have hNlt : (N : ℝ) ≤ ((N₀ : ℕ) : ℝ) := by
        exact_mod_cast (not_le.mp hbig).le
      have hsq : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N₀ : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt hNlt
      calc E ≤ 1 := hE1
        _ ≤ Real.sqrt ((N₀ : ℕ) : ℝ) / Real.sqrt (N : ℝ) := by
            rw [le_div_iff₀ hsqrtN, one_mul]
            exact hsq
        _ ≤ (C₁ + Real.sqrt (N₀ : ℝ)) / Real.sqrt (N : ℝ) := by
            rw [add_div]
            have h0 : 0 ≤ C₁ / Real.sqrt (N : ℝ) := div_nonneg hC₁0 hsqrtN.le
            linarith
  -- finish through M3
  refine le_trans hM3' ?_
  calc (Fintype.card S : ℝ) ^ 2 * E
      ≤ (Fintype.card S : ℝ) ^ 2
          * ((C₁ + Real.sqrt (N₀ : ℝ)) / Real.sqrt (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hEbound (by positivity)
    _ = (Fintype.card S : ℝ) ^ 2 * (C₁ + Real.sqrt (N₀ : ℝ))
          / Real.sqrt (N : ℝ) := by
        rw [mul_div_assoc]

