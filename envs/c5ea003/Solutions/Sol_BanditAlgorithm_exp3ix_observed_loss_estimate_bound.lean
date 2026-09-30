-- Prove2me | solution 1 for BanditAlgorithm.exp3ix_observed_loss_estimate_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:41:04.366944+00:00
-- url     : https://prove2.me/submissions/dadd79bb-1313-4e18-8b95-e90ef55e867f

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

/- Complete accepted proof by Harry_Xu, submission 491c5ec4-446d-44e6-a3aa-36c8c8fe8503, theorem 878049b0-45b9-4124-80a7-aa86dc8291e1. Body unchanged except final solution alias rename. -/

/-!
Direct-proof work for Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020),
Eq. (12.1), printed p. 165 / PDF p. 174, and Lemma 12.4, printed p. 169 /
PDF p. 178.  These are the pointwise increment, bias, and quadratic estimates
needed for the exponential-potential induction.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma expWeights_pos_ix {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    0 < expWeights s i := by
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp3IXProb_pos {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : 0 < exp3IXProb η γ m h i :=
  expWeights_pos_ix _ i

private lemma exp3IXProb_sum {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) : ∑ j, exp3IXProb η γ m h j = 1 := by
  rw [show (∑ j, exp3IXProb η γ m h j) =
      (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) /
        (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) by
    simp only [exp3IXProb, expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩))

private noncomputable def exp3IXIncrement {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) : ℝ :=
  if z.1 = i then (1 - z.2) / (exp3IXProb η γ m h i + γ) else 0

private lemma exp3IXEstimate_snoc {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) (i : Fin k) :
    exp3IXEstimate η γ (m + 1) (Fin.snoc h z) i =
      exp3IXEstimate η γ m h i + exp3IXIncrement η γ m h i z := by
  simp [exp3IXEstimate, exp3IXIncrement, exp3IXProb]

private lemma exp3IXIncrement_nonneg {k : ℕ} (η γ : ℝ) (hγ : 0 ≤ γ)
    (m : ℕ) (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ)
    (hz : z.2 ≤ 1) : 0 ≤ exp3IXIncrement η γ m h i z := by
  by_cases hzi : z.1 = i
  · simp only [exp3IXIncrement, if_pos hzi]
    exact div_nonneg (sub_nonneg.mpr hz)
      (add_nonneg (exp3IXProb_pos η γ m h i).le hγ)
  · simp [exp3IXIncrement, hzi]

private lemma exp3IXIncrement_le_inv_prob {k : ℕ} (η γ : ℝ) (hγ : 0 ≤ γ)
    (m : ℕ) (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ)
    (hz0 : 0 ≤ z.2) (hz1 : z.2 ≤ 1) :
    exp3IXIncrement η γ m h i z ≤ 1 / exp3IXProb η γ m h i := by
  have hp : 0 < exp3IXProb η γ m h i := exp3IXProb_pos η γ m h i
  by_cases hzi : z.1 = i
  · simp only [exp3IXIncrement, if_pos hzi]
    have hden : exp3IXProb η γ m h i ≤ exp3IXProb η γ m h i + γ :=
      le_add_of_nonneg_right hγ
    have hloss : 1 - z.2 ≤ 1 := by linarith
    calc
      (1 - z.2) / (exp3IXProb η γ m h i + γ) ≤
          1 / (exp3IXProb η γ m h i + γ) :=
        (div_le_div_iff_of_pos_right (lt_of_lt_of_le hp hden)).2 hloss
      _ ≤ 1 / exp3IXProb η γ m h i := by
        exact one_div_le_one_div_of_le hp hden
  · simp [exp3IXIncrement, hzi, hp.le]

private lemma exp3IX_bias_step {k : ℕ} (η γ : ℝ) (hγ : 0 < γ)
    (m : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    (1 - z.2) -
        ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z =
      γ * ∑ j, exp3IXIncrement η γ m h j z := by
  classical
  have hp : 0 < exp3IXProb η γ m h z.1 := exp3IXProb_pos η γ m h z.1
  have hden : exp3IXProb η γ m h z.1 + γ ≠ 0 :=
    ne_of_gt (add_pos hp hγ)
  have hinc :
      (∑ j, exp3IXIncrement η γ m h j z) =
        (1 - z.2) / (exp3IXProb η γ m h z.1 + γ) := by
    calc
      (∑ j, exp3IXIncrement η γ m h j z) =
          exp3IXIncrement η γ m h z.1 z := by
        apply Finset.sum_eq_single z.1
        · intro j hj hja
          simp [exp3IXIncrement, Ne.symm hja]
        · intro ha
          exact (ha (Finset.mem_univ z.1)).elim
      _ = _ := by simp [exp3IXIncrement]
  have hweighted :
      (∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z) =
        exp3IXProb η γ m h z.1 *
          ((1 - z.2) / (exp3IXProb η γ m h z.1 + γ)) := by
    calc
      (∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z) =
          exp3IXProb η γ m h z.1 * exp3IXIncrement η γ m h z.1 z := by
        apply Finset.sum_eq_single z.1
        · intro j hj hja
          simp [exp3IXIncrement, Ne.symm hja]
        · intro ha
          exact (ha (Finset.mem_univ z.1)).elim
      _ = _ := by simp [exp3IXIncrement]
  rw [hinc, hweighted]
  field_simp
  ring

private lemma exp3IX_quadratic_le_mass {k : ℕ} (η γ : ℝ) (hγ : 0 ≤ γ)
    (m : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ)
    (hz0 : 0 ≤ z.2) (hz1 : z.2 ≤ 1) :
    (∑ j, exp3IXProb η γ m h j * (exp3IXIncrement η γ m h j z) ^ 2) ≤
      ∑ j, exp3IXIncrement η γ m h j z := by
  classical
  apply Finset.sum_le_sum
  intro j hj
  have hp : 0 < exp3IXProb η γ m h j := exp3IXProb_pos η γ m h j
  have hy0 := exp3IXIncrement_nonneg η γ hγ m h j z hz1
  have hy1 := exp3IXIncrement_le_inv_prob η γ hγ m h j z hz0 hz1
  have hpy :
      exp3IXIncrement η γ m h j z * exp3IXProb η γ m h j ≤ 1 :=
    (le_div_iff₀ hp).mp hy1
  calc
    exp3IXProb η γ m h j * (exp3IXIncrement η γ m h j z) ^ 2 =
        (exp3IXIncrement η γ m h j z * exp3IXProb η γ m h j) *
          exp3IXIncrement η γ m h j z := by ring
    _ ≤ 1 * exp3IXIncrement η γ m h j z :=
      mul_le_mul_of_nonneg_right hpy hy0
    _ = exp3IXIncrement η γ m h j z := one_mul _

private lemma exp_le_quadratic_of_nonpos_ix (u : ℝ) (hu : u ≤ 0) :
    Real.exp u ≤ 1 + u + u ^ 2 / 2 := by
  let f : ℝ → ℝ := fun y ↦ 1 + y + y ^ 2 / 2 - Real.exp y
  have hfderiv : ∀ y : ℝ, HasDerivAt f (1 + y - Real.exp y) y := by
    intro y
    dsimp [f]
    convert ((((hasDerivAt_const y (1 : ℝ)).add (hasDerivAt_id y)).add
      ((hasDerivAt_id y).pow 2 |>.div_const 2)).sub (Real.hasDerivAt_exp y)) using 1 <;>
      first | rfl | (simp only [id_eq]; ring) | (funext z; simp only [id_eq, Pi.add_apply, Pi.sub_apply, Pi.pow_apply]; ring)
  have hfanti : Antitone f := by
    apply antitone_of_hasDerivAt_nonpos hfderiv
    intro y
    change 1 + y - Real.exp y ≤ 0
    linarith [Real.add_one_le_exp y]
  have hmono := hfanti hu
  dsimp [f] at hmono ⊢
  norm_num at hmono
  linarith

private lemma exp3IX_potential_ratio {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    (∑ j, Real.exp (-(η * exp3IXEstimate η γ (m + 1) (Fin.snoc h z) j))) /
        (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) =
      ∑ j, exp3IXProb η γ m h j *
        Real.exp (-(η * exp3IXIncrement η γ m h j z)) := by
  simp_rw [exp3IXEstimate_snoc]
  simp only [exp3IXProb, expWeights]
  rw [show (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j)) /
      (∑ a, Real.exp (-(η * exp3IXEstimate η γ m h a))) *
        Real.exp (-(η * exp3IXIncrement η γ m h j z))) =
      (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j)) *
        Real.exp (-(η * exp3IXIncrement η γ m h j z))) /
        (∑ a, Real.exp (-(η * exp3IXEstimate η γ m h a))) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    ring]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Real.exp_add]
  congr 1
  ring

private lemma exp3IX_potential_ratio_le {k : ℕ} (η γ : ℝ)
    (hη : 0 ≤ η) (hγ : 0 ≤ γ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ)
    (hz0 : 0 ≤ z.2) (hz1 : z.2 ≤ 1) (i0 : Fin k) :
    (∑ j, Real.exp (-(η * exp3IXEstimate η γ (m + 1) (Fin.snoc h z) j))) /
        (∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))) ≤
      Real.exp
        (-η * ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z +
          (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h j z) := by
  rw [exp3IX_potential_ratio]
  have hp (j : Fin k) : 0 ≤ exp3IXProb η γ m h j :=
    (exp3IXProb_pos η γ m h j).le
  have hy (j : Fin k) : 0 ≤ exp3IXIncrement η γ m h j z :=
    exp3IXIncrement_nonneg η γ hγ m h j z hz1
  have hquad := exp3IX_quadratic_le_mass η γ hγ m h z hz0 hz1
  calc
    (∑ j, exp3IXProb η γ m h j *
        Real.exp (-(η * exp3IXIncrement η γ m h j z))) ≤
        ∑ j, exp3IXProb η γ m h j *
          (1 - η * exp3IXIncrement η γ m h j z +
            (η ^ 2 / 2) * (exp3IXIncrement η γ m h j z) ^ 2) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hp j)
      convert exp_le_quadratic_of_nonpos_ix
        (-(η * exp3IXIncrement η γ m h j z))
        (neg_nonpos.mpr (mul_nonneg hη (hy j))) using 1 <;> first | rfl | ring
    _ = 1 +
        (-η * ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z +
          (η ^ 2 / 2) * ∑ j, exp3IXProb η γ m h j *
            (exp3IXIncrement η γ m h j z) ^ 2) := by
      have hsum := exp3IXProb_sum η γ m h i0
      calc
        (∑ j, exp3IXProb η γ m h j *
            (1 - η * exp3IXIncrement η γ m h j z +
              η ^ 2 / 2 * exp3IXIncrement η γ m h j z ^ 2)) =
            ∑ j, (exp3IXProb η γ m h j -
              η * (exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z) +
              (η ^ 2 / 2) * (exp3IXProb η γ m h j *
                exp3IXIncrement η γ m h j z ^ 2)) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsum,
            Finset.mul_sum, Finset.mul_sum]
          simp_rw [← Finset.mul_sum]
          ring
    _ ≤ 1 +
        (-η * ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z +
          (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h j z) := by
      gcongr
    _ ≤ Real.exp
        (-η * ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z +
          (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h j z) := by
      convert Real.add_one_le_exp
        (-η * ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z +
          (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h j z) using 1 <;> first | rfl | ring

private noncomputable def exp3IXMass {k : ℕ} (η γ : ℝ) :
    (n : ℕ) → BanditHistory k n → ℝ
  | 0, _ => 0
  | m + 1, h =>
      exp3IXMass η γ m (Fin.init h) +
        ∑ j, exp3IXIncrement η γ m (Fin.init h) j (h (Fin.last m))

private noncomputable def exp3IXMix {k : ℕ} (η γ : ℝ) :
    (n : ℕ) → BanditHistory k n → ℝ
  | 0, _ => 0
  | m + 1, h =>
      exp3IXMix η γ m (Fin.init h) +
        ∑ j, exp3IXProb η γ m (Fin.init h) j *
          exp3IXIncrement η γ m (Fin.init h) j (h (Fin.last m))

private noncomputable def exp3IXPotential {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) : ℝ :=
  ∑ j, Real.exp (-(η * exp3IXEstimate η γ m h j))

private lemma exp3IXMass_snoc {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    exp3IXMass η γ (m + 1) (Fin.snoc h z) =
      exp3IXMass η γ m h + ∑ j, exp3IXIncrement η γ m h j z := by
  simp [exp3IXMass]

private lemma exp3IXMix_snoc {k : ℕ} (η γ : ℝ) (m : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    exp3IXMix η γ (m + 1) (Fin.snoc h z) =
      exp3IXMix η γ m h +
        ∑ j, exp3IXProb η γ m h j * exp3IXIncrement η γ m h j z := by
  simp [exp3IXMix]

private lemma exp3IXPotential_pos {k : ℕ} (hk : 0 < k) (η γ : ℝ)
    (m : ℕ) (h : BanditHistory k m) : 0 < exp3IXPotential η γ m h := by
  unfold exp3IXPotential
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨Classical.choice (Fin.pos_iff_nonempty.mp hk),
      Finset.mem_univ _, Real.exp_pos _⟩

private lemma exp3IX_log_potential_bound {k : ℕ} (hk : 0 < k)
    (η γ : ℝ) (hη : 0 ≤ η) (hγ : 0 ≤ γ) :
    ∀ (m : ℕ) (h : BanditHistory k m),
      (∀ t : Fin m, (h t).2 ∈ Set.Icc (0 : ℝ) 1) →
      Real.log (exp3IXPotential η γ m h) ≤
        Real.log k - η * exp3IXMix η γ m h +
          (η ^ 2 / 2) * exp3IXMass η γ m h := by
  intro m
  induction m with
  | zero =>
      intro h hh
      simp [exp3IXPotential, exp3IXEstimate, exp3IXMix, exp3IXMass]
  | succ m ih =>
      intro h hh
      let h0 : BanditHistory k m := Fin.init h
      let z : Fin k × ℝ := h (Fin.last m)
      have hh0 : ∀ t : Fin m, (h0 t).2 ∈ Set.Icc (0 : ℝ) 1 := by
        intro t
        exact hh (Fin.castSucc t)
      have hz : z.2 ∈ Set.Icc (0 : ℝ) 1 := hh (Fin.last m)
      have hstep := exp3IX_potential_ratio_le η γ hη hγ m h0 z hz.1 hz.2
        (Classical.choice (Fin.pos_iff_nonempty.mp hk))
      have hratio : exp3IXPotential η γ (m + 1) h /
          exp3IXPotential η γ m h0 ≤
          Real.exp
            (-η * ∑ j, exp3IXProb η γ m h0 j * exp3IXIncrement η γ m h0 j z +
              (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h0 j z) := by
        simpa [exp3IXPotential, h0, z] using hstep
      have hnewpos := exp3IXPotential_pos hk η γ (m + 1) h
      have holdpos := exp3IXPotential_pos hk η γ m h0
      have hlogratio :
          Real.log (exp3IXPotential η γ (m + 1) h /
            exp3IXPotential η γ m h0) ≤
            -η * ∑ j, exp3IXProb η γ m h0 j * exp3IXIncrement η γ m h0 j z +
              (η ^ 2 / 2) * ∑ j, exp3IXIncrement η γ m h0 j z :=
        (Real.log_le_iff_le_exp (div_pos hnewpos holdpos)).2 hratio
      rw [Real.log_div hnewpos.ne' holdpos.ne'] at hlogratio
      have hi := ih h0 hh0
      have hsnoc : h = Fin.snoc h0 z := by simp [h0, z]
      rw [hsnoc] at hlogratio
      rw [hsnoc, exp3IXMix_snoc, exp3IXMass_snoc]
      ring_nf at hlogratio hi ⊢
      linarith

private lemma exp3IXMass_eq_estimate_sum {k : ℕ} (η γ : ℝ) :
    ∀ (m : ℕ) (h : BanditHistory k m),
      exp3IXMass η γ m h = ∑ j, exp3IXEstimate η γ m h j := by
  intro m
  induction m with
  | zero =>
      intro h
      simp [exp3IXMass, exp3IXEstimate]
  | succ m ih =>
      intro h
      let h0 : BanditHistory k m := Fin.init h
      let z : Fin k × ℝ := h (Fin.last m)
      have hsnoc : h = Fin.snoc h0 z := by simp [h0, z]
      rw [hsnoc, exp3IXMass_snoc]
      simp_rw [exp3IXEstimate_snoc]
      rw [Finset.sum_add_distrib, ih]

private lemma exp3IX_observed_minus_mix {k : ℕ} (η γ : ℝ) (hγ : 0 < γ) :
    ∀ (m : ℕ) (h : BanditHistory k m),
      (∑ t : Fin m, (1 - (h t).2)) - exp3IXMix η γ m h =
        γ * exp3IXMass η γ m h := by
  intro m
  induction m with
  | zero =>
      intro h
      simp [exp3IXMix, exp3IXMass]
  | succ m ih =>
      intro h
      let h0 : BanditHistory k m := Fin.init h
      let z : Fin k × ℝ := h (Fin.last m)
      have hsnoc : h = Fin.snoc h0 z := by simp [h0, z]
      have hb := exp3IX_bias_step η γ hγ m h0 z
      have hi := ih h0
      rw [hsnoc, exp3IXMix_snoc, exp3IXMass_snoc, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      linarith

private lemma exp3IX_mix_comparator_bound {k : ℕ} (hk : 1 < k)
    (η γ : ℝ) (hη : 0 < η) (hγ : 0 ≤ γ)
    (m : ℕ) (h : BanditHistory k m)
    (hh : ∀ t : Fin m, (h t).2 ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    exp3IXMix η γ m h - exp3IXEstimate η γ m h i ≤
      Real.log k / η + (η / 2) * exp3IXMass η γ m h := by
  have hk0 : 0 < k := Nat.zero_lt_of_lt hk
  have hterm : Real.exp (-(η * exp3IXEstimate η γ m h i)) ≤
      exp3IXPotential η γ m h := by
    unfold exp3IXPotential
    exact Finset.single_le_sum
      (fun j _ ↦ (Real.exp_pos (-(η * exp3IXEstimate η γ m h j))).le)
      (Finset.mem_univ i)
  have hcomp : -(η * exp3IXEstimate η γ m h i) ≤
      Real.log (exp3IXPotential η γ m h) :=
    (Real.le_log_iff_exp_le (exp3IXPotential_pos hk0 η γ m h)).2 hterm
  have hpot := exp3IX_log_potential_bound hk0 η γ hη.le hγ m h hh
  have hmain : η * (exp3IXMix η γ m h - exp3IXEstimate η γ m h i) ≤
      Real.log k + (η ^ 2 / 2) * exp3IXMass η γ m h := by
    nlinarith
  calc
    exp3IXMix η γ m h - exp3IXEstimate η γ m h i ≤
        (Real.log k + (η ^ 2 / 2) * exp3IXMass η γ m h) / η :=
      (le_div_iff₀ hη).2 (by simpa [mul_comm] using hmain)
    _ = Real.log k / η + (η / 2) * exp3IXMass η γ m h := by
      field_simp [hη.ne']

private theorem exp3IX_observed_loss_estimate_bound_scratch
    {k : ℕ} (hk : 1 < k) (n : ℕ) (η : ℝ) (hη : 0 < η)
    (h : BanditHistory k n)
    (hh : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    (∑ t : Fin n, (1 - (h t).2)) -
          (η / 2) * ∑ j : Fin k, exp3IXEstimate η (η / 2) n h j -
        exp3IXEstimate η (η / 2) n h i ≤
      Real.log k / η +
        (η / 2) * ∑ j : Fin k, exp3IXEstimate η (η / 2) n h j := by
  have hγ : 0 < η / 2 := half_pos hη
  have hmix := exp3IX_mix_comparator_bound hk η (η / 2) hη hγ.le n h hh i
  have hb := exp3IX_observed_minus_mix η (η / 2) hγ n h
  have hm := exp3IXMass_eq_estimate_sum η (η / 2) n h
  rw [hm] at hmix hb
  linarith

end BanditAlgorithm

theorem r6_accepted_pathwise_solution
    {k : ℕ} (hk : 1 < k) (n : ℕ)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η) (h : BanditAlgorithm.BanditHistory k n)
    (hh : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.adversarialRandomRegret n x h ≤
      Real.log k / η +
        (⨆ i : Fin k,
          BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
            ∑ t : Fin n, (1 - x t i)) +
        η * ∑ i : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h i := by
  classical
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_lt hk)
  let E : ℝ :=
    ∑ j : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h j
  let D : Fin k → ℝ := fun i ↦
    BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
      ∑ t : Fin n, (1 - x t i)
  have hcomp (i : Fin k) :
      (∑ t : Fin n, (1 - (h t).2)) - (η / 2) * E -
          BanditAlgorithm.exp3IXEstimate η (η / 2) n h i ≤
        Real.log k / η + (η / 2) * E :=
    BanditAlgorithm.exp3IX_observed_loss_estimate_bound_scratch hk n η hη h hh i
  have hDi (i : Fin k) : D i ≤ ⨆ j : Fin k, D j :=
    le_ciSup (Set.finite_range D).bddAbove i
  have hround_reward (i : Fin k) :
      (∑ t : Fin n, x t i) - ∑ t : Fin n, (h t).2 =
        (∑ t : Fin n, (1 - (h t).2)) - ∑ t : Fin n, (1 - x t i) := by
    simp_rw [Finset.sum_sub_distrib]
    simp
  rw [BanditAlgorithm.adversarialRandomRegret, sub_le_iff_le_add]
  apply ciSup_le
  intro i
  have hi :
      (∑ t : Fin n, x t i) - ∑ t : Fin n, (h t).2 ≤
        Real.log k / η + (⨆ j : Fin k, D j) + η * E := by
    rw [hround_reward i]
    dsimp [D] at hDi
    linarith [hcomp i, hDi i]
  linarith

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (η : ℝ) (hη : 0 < η)
    (h : BanditAlgorithm.BanditHistory k n)
    (hh : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    (∑ t : Fin n, (1 - (h t).2)) -
          (η / 2) *
            ∑ j : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h j -
        BanditAlgorithm.exp3IXEstimate η (η / 2) n h i ≤
      Real.log k / η +
        (η / 2) *
          ∑ j : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h j := by
  exact BanditAlgorithm.exp3IX_observed_loss_estimate_bound_scratch hk n η hη h hh i
