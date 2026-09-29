-- Prove2me | solution 1 for mme_released_interior_simultaneous_eventual_uniform_repair_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T08:16:27.409242+00:00
-- url     : https://prove2.me/submissions/a7cba936-a77f-4109-9d9d-8f9a932e0c3b

import Theorems.Thm_mme_released_interior_simultaneous_eventual_tensor_restriction
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
universe u

/-- The repair budget has logarithmic cost controlled by the capacity,
with the base-change factor exposed for choosing the repair scale. -/
private theorem mme_repair_budget_log_le (d C : ℕ) :
    Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤
      Real.log 8 + (Real.log 8 / Real.log d) * Real.log C := by
  have h := Real.natLog_le_logb C d
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h h8
  rw [Real.log_pow]
  simp only [Real.logb, Nat.cast_add, Nat.cast_one] at hm ⊢
  convert add_le_add_right hm (Real.log 8) using 1 <;> ring

/-- One repair scale makes its logarithmic cost an arbitrarily small
fraction of log capacity, uniformly over every natural capacity. -/
private theorem mme_repair_scale_exists_uniform_log_loss (delta : ℝ) (hdelta : 0 < delta) :
    ∃ d : ℕ, 1 < d ∧ ∀ C : ℕ,
      Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤ Real.log 8 + delta * Real.log C := by
  obtain ⟨s, hs⟩ := exists_nat_gt (1 / delta)
  let d := 8 ^ (s + 1)
  have hd : 1 < d := by
    dsimp [d]
    rw [pow_succ]
    have hp : 0 < 8 ^ s := pow_pos (by decide) _
    omega
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log (d : ℝ) = ((s : ℝ) + 1) * Real.log 8 := by
    simp [d, Nat.cast_pow, Real.log_pow]
  have hs' : 1 < (s : ℝ) * delta := (div_lt_iff₀ hdelta).mp hs
  have hratio : Real.log 8 / Real.log d ≤ delta := by
    apply (div_le_iff₀ (Real.log_pos hdR)).mpr
    rw [hlogd]
    nlinarith
  refine ⟨d, hd, fun C => (mme_repair_budget_log_le d C).trans ?_⟩
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg C))

/-- A common repair base and all sufficiently large scales give all interior
restrictions, while the logarithmic repair cost is bounded by any prescribed
positive fraction of log capacity, plus log eight. -/
theorem solution
    {KField : Type u} [Field KField] (delta : ℝ) (hdelta : 0 < delta) (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ᶠ k : ℕ in Filter.atTop,
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
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤ Real.log 8 + delta *
          Real.log (∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total s) reference)
            (fun c i => (c.2.val i).val) mu i)) := by
  classical
  obtain ⟨d, hd, hrepair⟩ := mme_repair_scale_exists_uniform_log_loss delta hdelta
  refine ⟨d, hd, ?_⟩
  filter_upwards [mme_released_interior_simultaneous_eventual_tensor_restriction
    (KField := KField) d hd eps heps] with k hsteps
  intro owner s hi
  obtain ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict, hcopies⟩ :=
    hsteps owner s hi
  refine ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict, hcopies, ?_⟩
  rw [hexponent]
  simpa only [Nat.cast_prod] using hrepair (∏ i : Fin 3,
    Nat.card (Block 2 (fullCell (parent_total s) reference)
      (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile owner s i c w) i))


#print axioms solution
