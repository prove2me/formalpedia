-- Prove2me | solution 1 for mme_released_joint_interior_eventual_entropy_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T10:47:41.316784+00:00
-- url     : https://prove2.me/submissions/5d56d52a-a344-4e19-9dfd-028ac2ce3539

import Theorems.Thm_mme_released_joint_interior_eventual_coordinate_repair
import Theorems.Thm_mme_regional_entropy_expression_log_rate
import Theorems.Thm_mme_regional_physical_entropy_selected_bound

open scoped BigOperators
open MME MME.ReleasedJointInterior MME.RecursiveYZ MME.RegionRealization
open MME.ProfiledCW MME.CompleteSplit MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter Topology

/-- A strict gap between an asymptotic logarithmic rate and a linear repair
cost eventually pays any fixed overhead. -/
private theorem mme_eventually_log_exceeds_linear_cost (B : ℕ → ℝ) (rate cost overhead : ℝ)
    (hlim : Tendsto (fun k => Real.log (B k) / (k : ℝ)) atTop (nhds rate))
    (hgap : cost < rate) :
    ∀ᶠ k : ℕ in atTop, overhead + cost * (k : ℝ) < Real.log (B k) := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun k => Real.log (B k) / (k : ℝ) - overhead / (k : ℝ))
      atTop (nhds rate) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using hlim.sub (hi.const_mul overhead)
  have hev := h.eventually (lt_mem_nhds hgap)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hkpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdiv : cost < (Real.log (B k) - overhead) / (k : ℝ) := by
    simpa only [sub_div] using hk
  have hmul := (lt_div_iff₀ hkR).mp hdiv
  linarith

/-- Rounding loses less than one copy, so the logarithm of the successor
retains the selected-count bound minus the exact repair cost. -/
private theorem mme_exact_step_log_successor_lower
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) (hpos : 0 < B) :
    Real.log B - Real.log ((8 : ℝ) ^ E.stage.repairExponent) <
      Real.log (E.copies + 1 : ℕ) := by
  have hd : 0 < 8 ^ E.stage.repairExponent := pow_pos (by decide) _
  have hn : E.count < 8 ^ E.stage.repairExponent * (E.copies + 1) := by
    have hmod := Nat.mod_lt E.count hd
    have h := Nat.mod_add_div E.count (8 ^ E.stage.repairExponent)
    dsimp [ExactStep.copies]
    nlinarith
  have hr : (E.count : ℝ) < (8 : ℝ) ^ E.stage.repairExponent *
      ((E.copies : ℝ) + 1) := by exact_mod_cast hn
  have hdR : 0 < (8 : ℝ) ^ E.stage.repairExponent := pow_pos (by norm_num) _
  have hdiv : B / (8 : ℝ) ^ E.stage.repairExponent < (E.copies : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (hB.trans_lt (by simpa only [mul_comm] using hr))
  have hlog := Real.log_lt_log (div_pos hpos hdR) hdiv
  rw [Real.log_div hpos.ne' hdR.ne'] at hlog
  simpa only [Nat.cast_add, Nat.cast_one] using hlog

private theorem polynomial_pos {R : ℕ} (n : Fin R → ℕ) (degree : ℕ) :
    0 < polynomialFactor n degree := by
  unfold polynomialFactor
  positivity

private theorem factor_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    0 < scaleFactor (half := half) (parent := parent) n d ell := by
  unfold scaleFactor loadFactor ambientFactor polynomialFactor
  positivity

private theorem size_scale (r : Fin 6) (k : ℕ) :
    size r k = fun j => k * size r 1 j := by
  funext j
  simp only [size, one_mul, Nat.mul_assoc]

private theorem counts_scale (r : Fin 6) (k : ℕ) :
    splitCount r k = fun j c => k * splitCount r 1 j c := by
  funext j c
  simp only [splitCount, one_mul, Nat.mul_assoc]

private theorem profile_scale (r : Fin 6) (k : ℕ) :
    integerProfile r k = fun i c w => k * integerProfile r 1 i c w := by
  funext i c w
  simp only [integerProfile, one_mul, Nat.mul_assoc]

-- The name linter unfolds the concrete released histogram tables.
set_option linter.constructorNameAsVariable false in
/-- The exact joint hashing steps approach the entropy rate computed by pooling
all 270 labels before taking the three-direction minimum. Repair and window
losses remain explicit. The successor count also covers nonpositive rates. -/
theorem solution
    (eta : ℝ) (heta : 0 < eta) (loss : ℝ) (hloss : 0 < loss)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
    let keep := fun (i : Fin 2)
      (_ : RecursiveXHash.Address 4 270 (parent r) (size r k)) =>
        parentTypical (parent_total r) (size r k) (splitCount r k)
          (integerProfile r k (yzMode i)) eps
    let Q := commonScale 4
      (loadNum (parent_total r) (splitCount r k) d
        (fun i => integerProfile r k (yzMode i)) keep) (loadDen (splitCount r k))
    ∃ reference : RecursiveXHash.Address 4 270 (parent r) (size r k),
      reference ∈ RecursiveXHash.target (n := size r k) (splitCount r k) ∧
      ∃ E : ExactStep 2 (blocks r k * 4) (gradedSource r k eps),
        ((RecursiveXHash.target (n := size r k) (splitCount r k)).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total r) reference)
            (fun c i => (c.2.val i).val) (integerProfile r k) i)) + 1 ∧
        (E.output = fun i x =>
          Graded (parent_total r) i reference
            (ProfiledCW.split (positions r k) (positions_length r k) x) ∧
          Useful (fullCell (parent_total r) reference) (integerProfile r k i)
            (ProfiledCW.split (positions r k) (positions_length r k) x)) ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
          Real.log 8 + eta * (blocks r k * 4 : ℕ) ∧
        (regionalRate (parent_total r) (size r 1) (splitCount r 1)
          (integerProfile r 1) - (blocks r 1 : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps -
          4 * eta * (blocks r 1 : ℝ) - loss) * (k : ℝ) <
            Real.log (E.copies + 1 : ℕ) := by
  classical
  obtain ⟨d, hd, hsteps⟩ :=
    mme_released_joint_interior_eventual_coordinate_repair eta heta eps heps
  refine ⟨d, hd, ?_⟩
  let factor := fun r k =>
    scaleFactor (half := 4) (parent := parent r) (size r k) d 2
  let rate := fun r => regionalRate (parent_total r) (size r 1)
    (splitCount r 1) (integerProfile r 1) - (blocks r 1 : ℝ) *
      entropyModulus (Fin 2 → CompleteWord 2) eps
  let B := fun r k => Real.exp
    (regionalRate (parent_total r) (size r k) (splitCount r k) (integerProfile r k) -
      (blocks r k : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
      4 * Real.sqrt (Real.log (factor r k) +
        scaleExponent (parent_total r) (size r k) (splitCount r k)
          (integerProfile r k) eps)) /
      (32 * polynomialFactor (size r k) (Fintype.card (Cell 4 270 (parent r))) * factor r k)
  have hlim (r : Fin 6) : Tendsto (fun k => Real.log (B r k) / (k : ℝ))
      atTop (nhds (rate r)) := by
    have h := mme_regional_entropy_expression_log_rate (parent_total r)
      (size r 1) (splitCount r 1) (integerProfile r 1) eps d
    change Tendsto (fun k => Real.log (B r k) / (k : ℝ)) atTop (nhds (rate r))
    simpa only [B, factor, rate, ← size_scale, ← counts_scale, ← profile_scale, blocks]
      using h
  have hlarge : ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      Real.log 8 + (rate r - loss) * (k : ℝ) < Real.log (B r k) :=
    Filter.eventually_all.mpr (fun r =>
      mme_eventually_log_exceeds_linear_cost (B r) (rate r)
        (rate r - loss) (Real.log 8) (hlim r) (by linarith))
  filter_upwards [hsteps, hlarge] with k hk hlarge
  intro r
  obtain ⟨reference, href, E, hcount, hexponent, houtput, hrepair⟩ := hk r
  refine ⟨reference, ?_, E, hcount, hexponent, houtput, hrepair, ?_⟩
  · unfold RecursiveXHash.target at href ⊢
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at href ⊢
    exact href
  · have hselected := mme_regional_physical_entropy_selected_bound
      (parent_total r) (size r k) (splitCount r k) (integerProfile r k)
      d eps heps.le reference (by
        unfold RecursiveXHash.target at href ⊢
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at href ⊢
        exact href)
    have hcountB : B r k ≤ (E.count : ℝ) := hselected.trans hcount
    have hf : 0 < factor r k := factor_pos (size r k) d 2
    have hp : 0 < polynomialFactor (size r k)
        (Fintype.card (Cell 4 270 (parent r))) := polynomial_pos _ _
    have hB : 0 < B r k :=
      div_pos (Real.exp_pos _) (mul_pos (mul_pos (by norm_num) hp) hf)
    have hround := mme_exact_step_log_successor_lower E hcountB hB
    have hblocks : blocks r k = k * blocks r 1 := by
      simp only [blocks, size, one_mul, Finset.mul_sum, Nat.mul_assoc]
    have hblocksR : ((blocks r k * 4 : ℕ) : ℝ) =
        4 * (k : ℝ) * (blocks r 1 : ℝ) := by
      rw [hblocks]
      push_cast
      ring
    have hrepair' := hrepair.trans_eq
      (congrArg (fun x : ℝ => Real.log 8 + eta * x) hblocksR)
    have hlog := hlarge r
    change (rate r - 4 * eta * (blocks r 1 : ℝ) - loss) * (k : ℝ) < _
    nlinarith only [hround, hrepair', hlog]


#print axioms solution
