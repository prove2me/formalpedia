-- Prove2me | solution 1 for mme_entropy_regional_smallN_outputs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-19T10:55:48.025485+00:00
-- url     : https://prove2.me/submissions/b6332b30-b493-44bc-a06a-19c23508d28b

import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_entropy_regional_CW_recipe
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen

open scoped BigOperators
open MME MME.CompleteSplit MME.RecursiveYZ MME.RegionRate MME.RegionRealization

set_option autoImplicit false

theorem solution : forall (N ell : Nat) (P : MME.ProfiledCW.Predicate N)
    (D : EntropyRecipe N ell P), N <= 2 -> D.inputs = 1 -> D.outputs <= 1 := by
  have analytic : ∀ (lower : Nat) (P : MME.ProfiledCW.Predicate 2)
      (S : IntegerStep lower 2 P), S.entropyCopies = 0 := by
    intro lower P S
    have hlen := S.length
    have hlow3 : lower < 3 := by
      by_contra h
      push_neg at h
      have h2 : 2 ≤ lower - 1 := by omega
      have h4 : 4 ≤ 2 ^ (lower - 1) := by
        calc (4 : Nat) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (lower - 1) := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
      cases heq : S.L with
      | zero =>
        rw [heq] at hlen
        simp at hlen
      | succ n =>
        have hge : 1 * 4 ≤ S.L * 2 ^ (lower - 1) :=
          Nat.mul_le_mul (by omega) h4
        omega
    have hne2 : lower ≠ 2 := by
      intro h2
      subst h2
      have hlength := S.length
      norm_num at hlength
      have hL : S.L = 1 := by omega
      let p := S.hashPositions 0
      let x : Position S.n := ⟨p.1, p.2, 0⟩
      let y : Position S.n := ⟨p.1, p.2, 1⟩
      have heq : S.positions.symm x = S.positions.symm y := by
        apply Fin.ext
        have hx := (S.positions.symm x).isLt
        have hy := (S.positions.symm y).isLt
        omega
      have hxy : x = y := S.positions.symm.injective heq
      have h01 := congrArg (fun z : Position S.n => z.2.2.val) hxy
      change (0 : Nat) = 1 at h01
      omega
    have hlow : lower = 0 ∨ lower = 1 := by omega
    have hL2 : S.L = 2 := by
      rcases hlow with rfl | rfl <;> norm_num at hlen <;> omega
    have hcard : Fintype.card (Position S.n) = 2 * ∑ r, S.n r := by
      unfold Position
      rw [Fintype.card_sigma]
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← Finset.sum_mul, Nat.mul_comm]
    have hocc : ∑ r, S.n r = 1 := by
      have he := Fintype.card_congr S.positions
      rw [Fintype.card_fin] at he
      rw [hcard, hL2] at he
      omega
    have hn1 : ∀ r : Fin S.R, S.n r = 1 := by
      intro r
      have h1 : 1 ≤ S.n r := by
        have h1 := S.parent_size r
        have h0 := S.minimum_pos
        omega
      have h2 : S.n r ≤ ∑ s, S.n s :=
        Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ r)
      omega
    have hCW3 : Fintype.card (CompleteWord lower) = 3 := by
      rcases hlow with rfl | rfl <;> decide
    have h9 : Fintype.card (Fin 2 → CompleteWord lower) = 9 := by
      simp [Fintype.card_pi_const, hCW3]
    classical
    have hsumM : ∀ r : Fin S.R, ∑ a, S.m r a = S.n r := by
      intro r
      have hj : ∀ a, MME.RecursiveThinSplit.count (S.reference r) a = S.m r a :=
        (Finset.mem_filter.mp S.reference_target).2 r
      calc ∑ a, S.m r a = ∑ a, MME.RecursiveThinSplit.count (S.reference r) a := by
            apply Finset.sum_congr rfl
            intro a _
            exact (hj a).symm
        _ = (Finset.univ : Finset (Fin (S.n r))).card := by
            show ∑ a, (Finset.univ.filter (fun j => S.reference r j = a)).card
              = (Finset.univ : Finset (Fin (S.n r))).card
            exact (Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)).symm
        _ = S.n r := by rw [Finset.card_univ, Fintype.card_fin]
    have hfreq : ∀ (r : Fin S.R) (c : Cell S.half S.R S.parent),
        (∑ w, S.mu 1 c w : ℕ) ≠ 0 → ∑ w, cellFrequency (S.mu 1) c w = 1 := by
      intro r c hne
      have hneR : ((∑ w, S.mu 1 c w : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hne
      unfold cellFrequency
      calc ∑ w, (S.mu 1 c w : ℝ) / (((∑ v, S.mu 1 c v : ℕ) : ℝ))
          = ∑ w, (S.mu 1 c w : ℝ) * ((((∑ v, S.mu 1 c v : ℕ) : ℝ))⁻¹) := by
            simp only [div_eq_mul_inv]
        _ = (∑ w, ((S.mu 1 c w : ℕ) : ℝ)) * ((((∑ v, S.mu 1 c v : ℕ) : ℝ))⁻¹) :=
            (Finset.sum_mul _ _ _).symm
        _ = 1 := by
            have hcs : (∑ w, ((S.mu 1 c w : ℕ) : ℝ)) = (((∑ w, S.mu 1 c w : ℕ)) : ℝ) := by
              exact_mod_cast rfl
            rw [hcs]
            exact mul_inv_cancel₀ hneR
    have hpair : ∀ (F F' : CompleteWord lower → ℝ),
        ∑ w : Fin 2 → CompleteWord lower, F (w 0) * F' (w 1)
        = (∑ a, F a) * (∑ b, F' b) := by
      intro F F'
      have e := Equiv.sum_comp (piFinTwoEquiv (fun _ => CompleteWord lower))
        (fun p : CompleteWord lower × CompleteWord lower => F p.1 * F' p.2)
      calc ∑ w : Fin 2 → CompleteWord lower, F (w 0) * F' (w 1)
          = ∑ p : CompleteWord lower × CompleteWord lower, F p.1 * F' p.2 := e
        _ = ∑ a, ∑ b, F a * F' b :=
            Fintype.sum_prod_type' (fun a b => F a * F' b)
        _ = (∑ a, F a) * (∑ b, F' b) :=
            (Fintype.sum_mul_sum _ _).symm
    have hmix1 : ∀ r : Fin S.R,
        ∑ w : Fin 2 → CompleteWord lower,
          parentMixture S.total S.n S.m (S.mu 1) r w = 1 := by
      intro r
      have hnr1 : ((S.n r : ℕ) : ℝ) = 1 := by exact_mod_cast hn1 r
      have hinner : ∀ c : MME.RecursiveThinSplit.Split S.half (S.parent r),
          (∑ w : Fin 2 → CompleteWord lower,
            ((S.m r c : ℕ) : ℝ) * cellFrequency (S.mu 1) ⟨r, c⟩ (w 0) *
              cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩ (w 1))
          = ((S.m r c : ℕ) : ℝ) := by
        intro c
        by_cases hm : S.m r c = 0
        · simp [hm]
        · have hpos : 0 < ∑ w, S.mu 1 ⟨r, c⟩ w := by
            have hm2 : (∑ w, S.mu 1 ⟨r, c⟩ w)
                = S.m r c + S.m r (complement (S.total r) c) :=
              S.mass 1 ⟨r, c⟩
            have hmc : 0 < S.m r c := Nat.pos_of_ne_zero hm
            omega
          have hpos' : 0 < ∑ w, S.mu 1 ⟨r, complement (S.total r) c⟩ w := by
            have hm2 : (∑ w, S.mu 1 ⟨r, complement (S.total r) c⟩ w)
                = S.m r (complement (S.total r) c) + S.m r c := by
              have h := S.mass 1 ⟨r, complement (S.total r) c⟩
              rw [complement_complement] at h
              exact h
            have hmc : 0 < S.m r c := Nat.pos_of_ne_zero hm
            omega
          have hF : ∑ a, cellFrequency (S.mu 1) ⟨r, c⟩ a = 1 :=
            hfreq r ⟨r, c⟩ (ne_of_gt hpos)
          have hF' : ∑ b, cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩ b = 1 :=
            hfreq r ⟨r, complement (S.total r) c⟩ (ne_of_gt hpos')
          calc ∑ w : Fin 2 → CompleteWord lower,
                  ((S.m r c : ℕ) : ℝ) * cellFrequency (S.mu 1) ⟨r, c⟩ (w 0) *
                    cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩ (w 1)
              = ((S.m r c : ℕ) : ℝ) * ∑ w : Fin 2 → CompleteWord lower,
                  cellFrequency (S.mu 1) ⟨r, c⟩ (w 0) *
                    cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩ (w 1) := by
                simp only [mul_assoc]
                exact (Finset.mul_sum _ _ _).symm
            _ = ((S.m r c : ℕ) : ℝ) * ((∑ a, cellFrequency (S.mu 1) ⟨r, c⟩ a) *
                  (∑ b, cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩ b)) := by
                rw [hpair (cellFrequency (S.mu 1) ⟨r, c⟩)
                  (cellFrequency (S.mu 1) ⟨r, complement (S.total r) c⟩)]
            _ = ((S.m r c : ℕ) : ℝ) := by simp [hF, hF']
      have hsumMR : ∑ c, ((S.m r c : ℕ) : ℝ) = ((S.n r : ℕ) : ℝ) := by
        exact_mod_cast hsumM r
      unfold parentMixture
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, Finset.sum_comm]
      simp only [hinner]
      rw [hsumMR, hnr1]
      norm_num
    have hnml : Real.negMulLog ((1 : ℝ) / 9) = Real.log 9 / 9 := by
      have e1 : Real.log ((1 : ℝ) / 9) = -Real.log 9 := by
        rw [one_div, Real.log_inv]
      show -((1 : ℝ) / 9) * Real.log ((1 : ℝ) / 9) = Real.log 9 / 9
      rw [e1]
      ring
    have hbits_nn : ∀ (C : Type) [Fintype C] [DecidableEq C]
        (mu' : C → CompleteWord lower → ℕ) (c : C),
        0 ≤ mme_modern_entropyBits
          (fun w => (mu' c w : ℝ) / ((∑ v, mu' c v : ℕ) : ℝ)) := by
      intro C _ _ mu' c
      unfold mme_modern_entropyBits
      apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
      apply Finset.sum_nonneg
      intro w _
      apply Real.negMulLog_nonneg
      · positivity
      · by_cases h0 : (∑ v, mu' c v : ℕ) = 0
        · simp [h0]
        · have hle : mu' c w ≤ ∑ v, mu' c v :=
            Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ _)
          have hleR : (mu' c w : ℝ) ≤ (((∑ v, mu' c v : ℕ)) : ℝ) := by
            exact_mod_cast hle
          exact (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero h0))).mpr hleR
    have hJlog : ∀ r : Fin S.R,
        entropy (parentMixture S.total S.n S.m (S.mu 1) r) ≤ Real.log 9 := by
      intro r
      have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin 2 → CompleteWord lower)),
          (0 : ℝ) ≤ (1 : ℝ) / 9 := fun _ _ => by norm_num
      have hw1 : ∑ _w : Fin 2 → CompleteWord lower, ((1 : ℝ) / 9) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, h9, nsmul_eq_mul]
        norm_num
      have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 2 → CompleteWord lower)),
          parentMixture S.total S.n S.m (S.mu 1) r i ∈ Set.Ici (0 : ℝ) := by
        intro i _
        unfold parentMixture cellFrequency
        rw [Set.mem_Ici]
        positivity
      have hJ := ConcaveOn.le_map_sum Real.concaveOn_negMulLog hw_nn hw1 hmem
      simp only [smul_eq_mul, Finset.mul_sum] at hJ
      have eL : (∑ x : Fin 2 → CompleteWord lower,
            (1 : ℝ) / 9 * Real.negMulLog (parentMixture S.total S.n S.m (S.mu 1) r x))
          = (1 / 9) * ∑ x, Real.negMulLog (parentMixture S.total S.n S.m (S.mu 1) r x) :=
        (Finset.mul_sum _ _ _).symm
      have eR : (∑ x : Fin 2 → CompleteWord lower,
            (1 : ℝ) / 9 * parentMixture S.total S.n S.m (S.mu 1) r x)
          = (1 / 9) * ∑ x, parentMixture S.total S.n S.m (S.mu 1) r x :=
        (Finset.mul_sum _ _ _).symm
      rw [eL, eR, hmix1 r, mul_one, hnml] at hJ
      have hent : entropy (parentMixture S.total S.n S.m (S.mu 1) r)
          = ∑ w, Real.negMulLog (parentMixture S.total S.n S.m (S.mu 1) r w) := rfl
      rw [hent]
      linarith [hJ]
    have hparent_le : parentPotential S.total S.n S.m (S.mu 1) ≤ Real.log 9 := by
      unfold parentPotential
      calc ∑ r, (S.n r : ℝ) * entropy (parentMixture S.total S.n S.m (S.mu 1) r)
          ≤ ∑ r, (S.n r : ℝ) * Real.log 9 := by
            apply Finset.sum_le_sum
            intro r _
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hJlog r
        _ = Real.log 9 := by
            rw [← Finset.sum_mul, ← Nat.cast_sum]
            have hoccR : ((∑ r, S.n r : ℕ) : ℝ) = 1 := by exact_mod_cast hocc
            rw [hoccR, one_mul]
    have hcompat_nn : 0 ≤ compatibilityPotential 0 (S.mu 1) := by
      unfold compatibilityPotential MME.RegionRealization.potential
      apply Finset.sum_nonneg
      intro c _
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact le_of_lt (Real.log_pos (by norm_num))
      · exact hbits_nn _
          (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (S.mu 1)) c
    have hE_le : regionalRate S.total S.n S.m S.mu ≤ Real.log 9 := by
      unfold regionalRate
      refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
      linarith [hparent_le, hcompat_nn]
    have hnml1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.negMulLog x ≤ 1 := by
      intro x hx0 hx1
      by_cases hx : x = 0
      · subst hx
        show -(0 : ℝ) * Real.log (0 : ℝ) ≤ 1
        simp
      · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
        have h1 : -Real.log x + 1 ≤ Real.exp (-Real.log x) := Real.add_one_le_exp _
        rw [Real.exp_neg, Real.exp_log hpos] at h1
        have h2 : -x * Real.log x + x ≤ 1 := by
          have h3 : (-Real.log x + 1) * x ≤ (x⁻¹) * x :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
          rw [inv_mul_cancel₀ (ne_of_gt hpos)] at h3
          linarith [h3, hx0]
        show -x * Real.log x ≤ 1
        linarith [h2, hx0]
    have hmod_nn : 0 ≤ entropyModulus (Fin 2 → CompleteWord lower) S.epsilon := by
      have hmem0 : (0 : ℝ) ∈ {z : ℝ | ∃ p q : (Fin 2 → CompleteWord lower) → ℝ,
          (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
          (∀ w, |p w - q w| ≤ S.epsilon) ∧ z = |entropy p - entropy q|} := by
        refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
        · intro w
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
        · intro w
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
        · intro w
          have heps : (0 : ℝ) ≤ S.epsilon := le_of_lt S.epsilon_pos
          simpa using heps
        · have e0 : entropy (fun _ : Fin 2 → CompleteWord lower => (0 : ℝ)) = 0 := by
            unfold entropy
            simp
          simp [e0]
      have hbdd : BddAbove {z : ℝ | ∃ p q : (Fin 2 → CompleteWord lower) → ℝ,
          (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
          (∀ w, |p w - q w| ≤ S.epsilon) ∧ z = |entropy p - entropy q|} := by
        refine ⟨2 * Fintype.card (Fin 2 → CompleteWord lower), fun z hz => ?_⟩
        obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
        have e1 : |entropy p| ≤ Fintype.card (Fin 2 → CompleteWord lower) := by
          calc |entropy p| ≤ ∑ w, |Real.negMulLog (p w)| := by
                unfold entropy
                exact Finset.abs_sum_le_sum_abs _ _
            _ = ∑ w, Real.negMulLog (p w) := by
                apply Finset.sum_congr rfl
                intro w _
                rw [abs_of_nonneg (Real.negMulLog_nonneg (hp w).1 (hp w).2)]
            _ ≤ ∑ _w : Fin 2 → CompleteWord lower, 1 :=
                Finset.sum_le_sum (fun w _ => hnml1 _ (hp w).1 (hp w).2)
            _ = _ := by simp
        have e2 : |entropy q| ≤ Fintype.card (Fin 2 → CompleteWord lower) := by
          calc |entropy q| ≤ ∑ w, |Real.negMulLog (q w)| := by
                unfold entropy
                exact Finset.abs_sum_le_sum_abs _ _
            _ = ∑ w, Real.negMulLog (q w) := by
                apply Finset.sum_congr rfl
                intro w _
                rw [abs_of_nonneg (Real.negMulLog_nonneg (hq w).1 (hq w).2)]
            _ ≤ ∑ _w : Fin 2 → CompleteWord lower, 1 :=
                Finset.sum_le_sum (fun w _ => hnml1 _ (hq w).1 (hq w).2)
            _ = _ := by simp
        calc |entropy p - entropy q| ≤ |entropy p| + |entropy q| := abs_sub _ _
          _ ≤ _ + _ := add_le_add e1 e2
          _ = 2 * Fintype.card (Fin 2 → CompleteWord lower) := by ring
      exact le_csSup hbdd hmem0
    have hpoly1 : 1 ≤ RegionRate.polynomialFactor S.n
        (Fintype.card (Cell S.half S.R S.parent)) := by
      unfold RegionRate.polynomialFactor
      have hb : ((∑ r, S.n r : ℕ) : ℝ) = 1 := by exact_mod_cast hocc
      rw [hb]
      norm_num
      exact one_le_pow₀ (by norm_num)
    have hfact1 : 1 ≤ RegionRate.scaleFactor (half := S.half) (parent := S.parent)
        S.n S.repairScale lower := by
      unfold RegionRate.scaleFactor
      have hload : 0 ≤ RegionRate.loadFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by
        unfold RegionRate.loadFactor RegionRate.ambientFactor RegionRate.polynomialFactor
        positivity
      have hhalf : (0 : ℝ) ≤ (S.half : ℕ) := by positivity
      linarith
    have hDpos : 0 < 32 * RegionRate.polynomialFactor S.n
        (Fintype.card (Cell S.half S.R S.parent)) *
        RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by
      have hp0 : 0 < RegionRate.polynomialFactor S.n
          (Fintype.card (Cell S.half S.R S.parent)) := by linarith [hpoly1]
      have hf0 : 0 < RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by linarith [hfact1]
      exact mul_pos (mul_pos (by norm_num) hp0) hf0
    have hXle : regionalRate S.total S.n S.m S.mu -
        ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
        4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) ≤ Real.log 9 := by
      have hloss : 0 ≤ ((∑ r, S.n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord lower) S.epsilon := by
        apply mul_nonneg _ hmod_nn
        positivity
      have hsqrt : 0 ≤ 4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half)
          (parent := S.parent) S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) := by
        apply mul_nonneg _ (by positivity)
        norm_num
      linarith [hE_le, hloss, hsqrt]
    have hexp9 : Real.exp (regionalRate S.total S.n S.m S.mu -
        ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
        4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon)) ≤ 9 := by
      have h1 : regionalRate S.total S.n S.m S.mu -
          ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
          4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
            S.n S.repairScale lower) +
            RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) ≤ Real.log 9 :=
        hXle
      calc Real.exp _ ≤ Real.exp (Real.log 9) := Real.exp_le_exp.mpr h1
        _ = 9 := Real.exp_log (by norm_num)
    have hfin : S.entropyLower < 1 := by
      show (Real.exp (regionalRate S.total S.n S.m S.mu -
            ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
            4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
              S.n S.repairScale lower) +
              RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon))) /
          (32 * RegionRate.polynomialFactor S.n (Fintype.card (Cell S.half S.R S.parent)) *
            RegionRate.scaleFactor (half := S.half) (parent := S.parent) S.n S.repairScale lower)
        < 1
      have hnum : Real.exp (regionalRate S.total S.n S.m S.mu -
            ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
            4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
              S.n S.repairScale lower) +
              RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon)) ≤ 9 :=
        hexp9
      have hden : (32 : ℝ) ≤ 32 * RegionRate.polynomialFactor S.n
          (Fintype.card (Cell S.half S.R S.parent)) *
          RegionRate.scaleFactor (half := S.half) (parent := S.parent)
            S.n S.repairScale lower := by
        nlinarith [hpoly1, hfact1]
      rw [div_lt_one hDpos]
      linarith [hnum, hden]
    have hfloor : ⌊S.entropyLower⌋₊ = 0 := Nat.floor_eq_zero.mpr hfin
    have hcopies0 : S.entropyCopies = 0 := by
      show ⌊S.entropyLower⌋₊ / 8 ^ S.repairExponent = 0
      rw [hfloor]
      simp
    exact hcopies0
  have analytic0 : ∀ (lower : Nat) (P : MME.ProfiledCW.Predicate 0)
      (S : IntegerStep lower 0 P), S.entropyCopies = 0 := by
    intro lower P S
    classical
    have hcard : Fintype.card (Position S.n) = 2 * ∑ r, S.n r := by
      unfold Position
      rw [Fintype.card_sigma]
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← Finset.sum_mul, Nat.mul_comm]
    have hnml : Real.negMulLog ((1 : ℝ) / 9) = Real.log 9 / 9 := by
      have e1 : Real.log ((1 : ℝ) / 9) = -Real.log 9 := by
        rw [one_div, Real.log_inv]
      show -((1 : ℝ) / 9) * Real.log ((1 : ℝ) / 9) = Real.log 9 / 9
      rw [e1]
      ring
    have hbits_nn : ∀ (C : Type) [Fintype C] [DecidableEq C]
        (mu' : C → CompleteWord lower → ℕ) (c : C),
        0 ≤ mme_modern_entropyBits
          (fun w => (mu' c w : ℝ) / ((∑ v, mu' c v : ℕ) : ℝ)) := by
      intro C _ _ mu' c
      unfold mme_modern_entropyBits
      apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
      apply Finset.sum_nonneg
      intro w _
      apply Real.negMulLog_nonneg
      · positivity
      · by_cases h0 : (∑ v, mu' c v : ℕ) = 0
        · simp [h0]
        · have hle : mu' c w ≤ ∑ v, mu' c v :=
            Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ _)
          have hleR : (mu' c w : ℝ) ≤ (((∑ v, mu' c v : ℕ)) : ℝ) := by
            exact_mod_cast hle
          exact (div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero h0))).mpr hleR
    have hnml1 : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → Real.negMulLog x ≤ 1 := by
      intro x hx0 hx1
      by_cases hx : x = 0
      · subst hx
        show -(0 : ℝ) * Real.log (0 : ℝ) ≤ 1
        simp
      · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
        have h1 : -Real.log x + 1 ≤ Real.exp (-Real.log x) := Real.add_one_le_exp _
        rw [Real.exp_neg, Real.exp_log hpos] at h1
        have h2 : -x * Real.log x + x ≤ 1 := by
          have h3 : (-Real.log x + 1) * x ≤ (x⁻¹) * x :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt hpos)
          rw [inv_mul_cancel₀ (ne_of_gt hpos)] at h3
          linarith [h3, hx0]
        show -x * Real.log x ≤ 1
        linarith [h2, hx0]
    have hcompat_nn : 0 ≤ compatibilityPotential 0 (S.mu 1) := by
      unfold compatibilityPotential MME.RegionRealization.potential
      apply Finset.sum_nonneg
      intro c _
      apply mul_nonneg
      · apply mul_nonneg
        · positivity
        · exact le_of_lt (Real.log_pos (by norm_num))
      · exact hbits_nn _
          (partCount (yzBoundary 0) (modeGroup (yzMode 0)) (S.mu 1)) c
    have hmod_nn : 0 ≤ entropyModulus (Fin 2 → CompleteWord lower) S.epsilon := by
      have hmem0 : (0 : ℝ) ∈ {z : ℝ | ∃ p q : (Fin 2 → CompleteWord lower) → ℝ,
          (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
          (∀ w, |p w - q w| ≤ S.epsilon) ∧ z = |entropy p - entropy q|} := by
        refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_, ?_⟩
        · intro w
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
        · intro w
          exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
        · intro w
          have heps : (0 : ℝ) ≤ S.epsilon := le_of_lt S.epsilon_pos
          simpa using heps
        · have e0 : entropy (fun _ : Fin 2 → CompleteWord lower => (0 : ℝ)) = 0 := by
            unfold entropy
            simp
          simp [e0]
      have hbdd : BddAbove {z : ℝ | ∃ p q : (Fin 2 → CompleteWord lower) → ℝ,
          (∀ w, p w ∈ Set.Icc 0 1) ∧ (∀ w, q w ∈ Set.Icc 0 1) ∧
          (∀ w, |p w - q w| ≤ S.epsilon) ∧ z = |entropy p - entropy q|} := by
        refine ⟨2 * Fintype.card (Fin 2 → CompleteWord lower), fun z hz => ?_⟩
        obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
        have e1 : |entropy p| ≤ Fintype.card (Fin 2 → CompleteWord lower) := by
          calc |entropy p| ≤ ∑ w, |Real.negMulLog (p w)| := by
                unfold entropy
                exact Finset.abs_sum_le_sum_abs _ _
            _ = ∑ w, Real.negMulLog (p w) := by
                apply Finset.sum_congr rfl
                intro w _
                rw [abs_of_nonneg (Real.negMulLog_nonneg (hp w).1 (hp w).2)]
            _ ≤ ∑ _w : Fin 2 → CompleteWord lower, 1 :=
                Finset.sum_le_sum (fun w _ => hnml1 _ (hp w).1 (hp w).2)
            _ = _ := by simp
        have e2 : |entropy q| ≤ Fintype.card (Fin 2 → CompleteWord lower) := by
          calc |entropy q| ≤ ∑ w, |Real.negMulLog (q w)| := by
                unfold entropy
                exact Finset.abs_sum_le_sum_abs _ _
            _ = ∑ w, Real.negMulLog (q w) := by
                apply Finset.sum_congr rfl
                intro w _
                rw [abs_of_nonneg (Real.negMulLog_nonneg (hq w).1 (hq w).2)]
            _ ≤ ∑ _w : Fin 2 → CompleteWord lower, 1 :=
                Finset.sum_le_sum (fun w _ => hnml1 _ (hq w).1 (hq w).2)
            _ = _ := by simp
        calc |entropy p - entropy q| ≤ |entropy p| + |entropy q| := abs_sub _ _
          _ ≤ _ + _ := add_le_add e1 e2
          _ = 2 * Fintype.card (Fin 2 → CompleteWord lower) := by ring
      exact le_csSup hbdd hmem0
    have hfact1 : 1 ≤ RegionRate.scaleFactor (half := S.half) (parent := S.parent)
        S.n S.repairScale lower := by
      unfold RegionRate.scaleFactor
      have hload : 0 ≤ RegionRate.loadFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by
        unfold RegionRate.loadFactor RegionRate.ambientFactor RegionRate.polynomialFactor
        positivity
      have hhalf : (0 : ℝ) ≤ (S.half : ℕ) := by positivity
      linarith
    have hL0 : S.L = 0 := by
      have h := S.length
      rcases Nat.mul_eq_zero.mp h with h | h
      · exact h
      · have h1 : 1 ≤ 2 ^ (lower - 1) := one_le_pow₀ (by norm_num)
        omega
    have hocc0 : ∑ r, S.n r = 0 := by
      have he := Fintype.card_congr S.positions
      rw [Fintype.card_fin, hcard, hL0] at he
      omega
    have hnr0 : ∀ r : Fin S.R, S.n r = 0 := by
      intro r
      have h2 : S.n r ≤ ∑ s, S.n s :=
        Finset.single_le_sum (fun s _ => Nat.zero_le _) (Finset.mem_univ r)
      omega
    have hpoly1 : 1 ≤ RegionRate.polynomialFactor S.n
        (Fintype.card (Cell S.half S.R S.parent)) := by
      unfold RegionRate.polynomialFactor
      have hb : ((∑ r, S.n r : ℕ) : ℝ) = 0 := by exact_mod_cast hocc0
      rw [hb]
      norm_num
      exact one_le_pow₀ (by norm_num)
    have hDpos : 0 < 32 * RegionRate.polynomialFactor S.n
        (Fintype.card (Cell S.half S.R S.parent)) *
        RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by
      have hp0 : 0 < RegionRate.polynomialFactor S.n
          (Fintype.card (Cell S.half S.R S.parent)) := by linarith [hpoly1]
      have hf0 : 0 < RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower := by linarith [hfact1]
      exact mul_pos (mul_pos (by norm_num) hp0) hf0
    have hparent0 : parentPotential S.total S.n S.m (S.mu 1) = 0 := by
      unfold parentPotential
      apply Finset.sum_eq_zero
      intro r _
      have hr : ((S.n r : ℕ) : ℝ) = 0 := by exact_mod_cast hnr0 r
      rw [hr]
      exact zero_mul _
    have hE0 : regionalRate S.total S.n S.m S.mu ≤ 0 := by
      unfold regionalRate
      refine le_trans (min_le_right _ _) (le_trans (min_le_left _ _) ?_)
      linarith [hparent0, hcompat_nn]
    have hX0 : regionalRate S.total S.n S.m S.mu -
        ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
        4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) ≤ 0 := by
      have hloss : 0 ≤ ((∑ r, S.n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord lower) S.epsilon := by
        apply mul_nonneg _ hmod_nn
        positivity
      have hsqrt : 0 ≤ 4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half)
          (parent := S.parent) S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) := by
        apply mul_nonneg _ (by positivity)
        norm_num
      linarith [hE0, hloss, hsqrt]
    have hexp0 : Real.exp (regionalRate S.total S.n S.m S.mu -
        ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
        4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
          S.n S.repairScale lower) +
          RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon)) ≤ 1 := by
      have h1 : regionalRate S.total S.n S.m S.mu -
          ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
          4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
            S.n S.repairScale lower) +
            RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) ≤ 0 :=
        hX0
      calc Real.exp _ ≤ Real.exp 0 := Real.exp_le_exp.mpr h1
        _ = 1 := Real.exp_zero
    have hfin0 : S.entropyLower < 1 := by
      show (Real.exp (regionalRate S.total S.n S.m S.mu -
            ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
            4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
              S.n S.repairScale lower) +
              RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon))) /
          (32 * RegionRate.polynomialFactor S.n (Fintype.card (Cell S.half S.R S.parent)) *
            RegionRate.scaleFactor (half := S.half) (parent := S.parent) S.n S.repairScale lower)
        < 1
      have hnum : Real.exp (regionalRate S.total S.n S.m S.mu -
            ((∑ r, S.n r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord lower) S.epsilon -
            4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half) (parent := S.parent)
              S.n S.repairScale lower) +
              RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon)) ≤ 1 :=
        hexp0
      have hden : (32 : ℝ) ≤ 32 * RegionRate.polynomialFactor S.n
          (Fintype.card (Cell S.half S.R S.parent)) *
          RegionRate.scaleFactor (half := S.half) (parent := S.parent)
            S.n S.repairScale lower := by
        nlinarith [hpoly1, hfact1]
      rw [div_lt_one hDpos]
      linarith [hnum, hden]
    have hfloor0 : ⌊S.entropyLower⌋₊ = 0 := Nat.floor_eq_zero.mpr hfin0
    have hcopies00 : S.entropyCopies = 0 := by
      show ⌊S.entropyLower⌋₊ / 8 ^ S.repairExponent = 0
      rw [hfloor0]
      simp
    exact hcopies00
  have analytic1 : ∀ (lower : Nat) (P : MME.ProfiledCW.Predicate 1)
      (S : IntegerStep lower 1 P), False := by
    intro lower P S
    have hlen := S.length
    have hlow3 : lower < 3 := by
      by_contra h
      have hle : 3 ≤ lower := by omega
      have h2 : 2 ≤ lower - 1 := by omega
      have h4 : 4 ≤ 2 ^ (lower - 1) := by
        calc (4 : Nat) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (lower - 1) := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h2
      cases heq : S.L with
      | zero =>
        rw [heq] at hlen
        simp at hlen
      | succ n =>
        have hge : 1 * 4 ≤ S.L * 2 ^ (lower - 1) :=
          Nat.mul_le_mul (by omega) h4
        omega
    have hne2 : lower ≠ 2 := by
      intro h2
      subst h2
      have hlength := S.length
      have e : (2 : Nat) ^ (2 - 1) = 2 := by norm_num
      rw [e] at hlength
      omega
    have hlow : lower = 0 ∨ lower = 1 := by omega
    have hL1 : S.L = 1 := by
      rcases hlow with rfl | rfl <;> norm_num at hlen <;> omega
    have hcard1 : Fintype.card (Position S.n) = 2 * ∑ r, S.n r := by
      unfold Position
      rw [Fintype.card_sigma]
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← Finset.sum_mul, Nat.mul_comm]
    have hcontra : (1 : Nat) = 2 * ∑ r, S.n r := by
      have he := Fintype.card_congr S.positions
      rw [Fintype.card_fin, hcard1, hL1] at he
      exact he
    omega
  have analytic_le : ∀ {N : Nat} (lower : Nat) (P : MME.ProfiledCW.Predicate N)
      (S : IntegerStep lower N P), N ≤ 2 → S.entropyCopies = 0 := by
    intro N lower P S hN
    have hN210 : N = 0 ∨ N = 1 ∨ N = 2 := by omega
    rcases hN210 with rfl | rfl | rfl
    · exact analytic0 _ _ S
    · exact False.elim (analytic1 _ _ S)
    · exact analytic _ _ S
  have key : forall {N ell : Nat} {P : MME.ProfiledCW.Predicate N}
      (D : EntropyRecipe N ell P), N <= 2 -> D.inputs = 1 -> D.outputs <= 1 := by
    intro N ell P D hN hi
    induction D with
    | boundary B =>
      simp only [EntropyRecipe.outputs]
      exact le_rfl
    | descend hdown types copies steps enough inside cover next ih =>
      simp only [EntropyRecipe.inputs] at hi
      have htdvd : types ∣ 1 := ⟨next.inputs, hi.symm⟩
      have ht : types = 1 := Nat.dvd_one.mp htdvd
      have hnvdvd : next.inputs ∣ 1 := ⟨types, hi.symm.trans (Nat.mul_comm _ _)⟩
      have hni : next.inputs = 1 := Nat.dvd_one.mp hnvdvd
      subst ht
      have hcop0 : copies = 0 := by
        have h0 := enough (0 : Fin 1)
        have hz : (steps (0 : Fin 1)).entropyCopies = 0 := analytic_le _ _ _ hN
        omega
      simp only [EntropyRecipe.outputs]
      rw [hcop0, Nat.zero_mul]
      exact Nat.zero_le _
    | partition size positions Q inside children ih =>
      simp only [EntropyRecipe.inputs] at hi
      have hcard2 := by
        have he := Fintype.card_congr positions
        rw [Fintype.card_fin, Fintype.card_sigma] at he
        simpa using he
      have hsz : forall i, size i <= 2 := by
        intro i
        have hle : size i <= ∑ j, size j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      have hall : forall i, (children i).inputs = 1 := by
        intro i
        have hdvd : (children i).inputs ∣ ∏ j, (children j).inputs :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        rw [hi] at hdvd
        exact Nat.dvd_one.mp hdvd
      have h1 : forall i, (children i).outputs <= 1 :=
        fun i => ih i (hsz i) (hall i)
      exact Finset.prod_le_one (fun i _ => Nat.zero_le _) (fun i _ => h1 i)
    | rotate child ih =>
      simp only [EntropyRecipe.inputs, EntropyRecipe.outputs] at hi ⊢
      exact ih hN hi
    | swap child ih =>
      simp only [EntropyRecipe.inputs, EntropyRecipe.outputs] at hi ⊢
      exact ih hN hi
  intro N ell P D hN hi
  exact key D hN hi
