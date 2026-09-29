-- Prove2me | solution 1 for mme_released_interior_simultaneous_entropy_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:55:24.285182+00:00
-- url     : https://prove2.me/submissions/c9c26190-7f9d-4873-bb8b-1481dcbbc685

import Theorems.Thm_mme_released_interior_simultaneous_coordinate_repair_restriction
import Theorems.Thm_mme_regional_entropy_expression_log_rate
import Theorems.Thm_mme_regional_physical_entropy_selected_bound
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate Filter Topology
open scoped Classical
universe u

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

/-- Simultaneous interior restrictions approach their regional entropy rates
at every positive tolerance. The successor copy count keeps the statement valid
without assuming positivity of the regional rate. -/
theorem solution
    (stride : ℕ) (hstride : 0 < stride)
    {KField : Type u} [Field KField] (loss : ℝ) (hloss : 0 < loss) (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
    ∀ (owner : Fin 6) (s : Fin 45), (seed owner s).boundary = [] →
    let n := fun r : Fin 6 => k * (regionalSize owner s) r
    let m := fun r c => k * (splitCount owner s) r c
    let mu := fun i c w => k * (integerProfile owner s) i c w
    let source : Predicate ((k * denominator ^ 4) * 4) := fun i x =>
      (∀ p : Fin (k * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) = (parent s) 0 i) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (k * denominator ^ 4) //
            ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) /
            (k * denominator ^ 4 : ℕ) -
          ((((ReleasedGlobal.jointRows owner s).map
            (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ) ^ 4| ≤ eps
    let keep := fun (i : Fin 2) (_ : Address 4 6 (parent s) n) =>
      parentTypical (parent_total s) n m (mu (yzMode i)) eps
    let Q := commonScale 4 (loadNum (parent_total s) m d (fun i => mu (yzMode i)) keep) (loadDen m)
    ∃ (positions : Fin ((k * denominator ^ 4) * 2) ≃ Position n)
      (reference : Address 4 6 (parent s) n), reference ∈ RecursiveXHash.target m ∧
      ∃ E : ExactStep 2 ((k * denominator ^ 4) * 4) source,
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total s) reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        (E.output = fun i x => Graded (parent_total s) i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell (parent_total s) reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) ) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin E.copies => tensor KField E.output))
          (tensor KField source) ∧
        (((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) /
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤ Real.log 8 +
          (loss / (8 * (denominator : ℝ) ^ 4)) * (4 * (k * denominator ^ 4) : ℕ) ∧
        (regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
          (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps - loss) * (k : ℝ) <
          Real.log (E.copies + 1 : ℕ) := by
  classical
  have hden : 0 < (denominator : ℝ) := by norm_num [denominator]
  let eta : ℝ := loss / (8 * (denominator : ℝ) ^ 4)
  have heta : 0 < eta := div_pos hloss (mul_pos (by norm_num) (pow_pos hden _))
  obtain ⟨d, hd, hcofinal⟩ :=
    mme_released_interior_simultaneous_coordinate_repair_restriction
      stride hstride (KField := KField) eta heta eps heps
  refine ⟨d, hd, ?_⟩
  let size := fun (owner : Fin 6) (s : Fin 45) (k : ℕ) r => k * regionalSize owner s r
  let counts := fun (owner : Fin 6) (s : Fin 45) (k : ℕ) r c => k * splitCount owner s r c
  let profiles := fun (owner : Fin 6) (s : Fin 45) (k : ℕ) i c w =>
    k * integerProfile owner s i c w
  let factor := fun owner s k =>
    scaleFactor (half := 4) (parent := parent s) (size owner s k) d 2
  let rate := fun owner s =>
    regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
      (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
      entropyModulus (Fin 2 → CompleteWord 2) eps
  let B := fun owner s k => Real.exp
    (regionalRate (parent_total s) (size owner s k) (counts owner s k) (profiles owner s k) -
      ((∑ r, size owner s k r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
      4 * Real.sqrt (Real.log (factor owner s k) +
        scaleExponent (parent_total s) (size owner s k) (counts owner s k)
          (profiles owner s k) eps)) /
      (32 * polynomialFactor (size owner s k) (Fintype.card (Cell 4 6 (parent s))) *
        factor owner s k)
  have hev (owner : Fin 6) (s : Fin 45) : ∀ᶠ k : ℕ in atTop,
      Real.log 8 + (rate owner s - loss / 2) * (k : ℝ) < Real.log (B owner s k) := by
    have hlim := mme_regional_entropy_expression_log_rate (parent_total s)
      (regionalSize owner s) (splitCount owner s) (integerProfile owner s) eps d
    exact mme_eventually_log_exceeds_linear_cost (B owner s) (rate owner s)
      (rate owner s - loss / 2) (Real.log 8) hlim (by linarith)
  have hall : ∀ᶠ k : ℕ in atTop, ∀ owner : Fin 6, ∀ s : Fin 45,
      Real.log 8 + (rate owner s - loss / 2) * (k : ℝ) < Real.log (B owner s k) := by
    exact Filter.eventually_all.mpr (fun owner => Filter.eventually_all.mpr (hev owner))
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hall
  intro K
  obtain ⟨k, hK, hk, heven, hmultiple, hsteps⟩ := hcofinal (max K K0)
  refine ⟨k, (le_max_left K K0).trans hK, hk, heven, hmultiple, ?_⟩
  intro owner s hi
  obtain ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, hrepair⟩ := hsteps owner s hi
  refine ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, hrepair, ?_⟩
  have hselected := mme_regional_physical_entropy_selected_bound
    (parent_total s) (size owner s k) (counts owner s k) (profiles owner s k)
    d eps heps.le reference href
  have hcountB : B owner s k ≤ (E.count : ℝ) := hselected.trans hcount
  have hf : 0 < factor owner s k := by
    dsimp [factor, scaleFactor, loadFactor, ambientFactor, polynomialFactor]
    positivity
  have hp : 0 < polynomialFactor (size owner s k)
      (Fintype.card (Cell 4 6 (parent s))) := by
    unfold polynomialFactor
    positivity
  have hB : 0 < B owner s k :=
    div_pos (Real.exp_pos _) (mul_pos (mul_pos (by norm_num) hp) hf)
  have hround := mme_exact_step_log_successor_lower E hcountB hB
  have hbudget : Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
      Real.log 8 + loss / 2 * (k : ℝ) := by
    convert hrepair using 1
    dsimp [eta]
    push_cast
    field_simp
    ring
  have hlog := hK0 k ((le_max_right K K0).trans hK) owner s
  change (rate owner s - loss) * (k : ℝ) < _
  nlinarith only [hround, hbudget, hlog]


#print axioms solution
