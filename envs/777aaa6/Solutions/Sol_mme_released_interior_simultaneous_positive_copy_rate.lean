-- Prove2me | solution 1 for mme_released_interior_simultaneous_positive_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:01:43.828549+00:00
-- url     : https://prove2.me/submissions/24235952-824a-4fc2-b1b3-d8b725c5ae88

import Theorems.Thm_mme_released_interior_simultaneous_entropy_copy_rate
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells MME.RegionRate
open scoped Classical
universe u

/-- Once a positive rate exceeds the rounding allowance, a successor-count
bound gives a positive count and loses at most one additional rate allowance. -/
private theorem mme_log_successor_implies_positive_rate
    (n : ℕ) (rate loss k : ℝ) (hloss : 0 < loss) (hk : 0 < k)
    (hlarge : Real.log 2 ≤ loss * k)
    (hlog : (rate - loss) * k < Real.log (n + 1 : ℕ))
    (hrate : 2 * loss < rate) :
    0 < n ∧ (rate - 2 * loss) * k < Real.log n := by
  have hpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0] at hlog
    norm_num at hlog
    have hp : 0 < (rate - loss) * k := mul_pos (by linarith) hk
    linarith
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hpos
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
  have hs : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    linarith
  have hup := Real.log_le_log (by positivity : (0 : ℝ) < (n + 1 : ℕ)) hs
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hup
  refine ⟨hpos, ?_⟩
  nlinarith only [hlog, hup, hlarge]

/-- All interior restrictions share a cofinal scale. Wherever the regional
entropy rate exceeds the tolerance penalty and twice the prescribed loss,
the restriction has positive exponentially many copies with that rate margin. -/
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
          Real.log (E.copies + 1 : ℕ) ∧
        (2 * loss < (regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
          (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps) →
          0 < E.copies ∧ ((regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
          (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps) - 2 * loss) * (k : ℝ) <
            Real.log E.copies) := by
  classical
  obtain ⟨d, hd, hcofinal⟩ := mme_released_interior_simultaneous_entropy_copy_rate
    stride hstride (KField := KField) loss hloss eps heps
  obtain ⟨K0, hK0⟩ := exists_nat_gt (Real.log 2 / loss)
  refine ⟨d, hd, ?_⟩
  intro K
  obtain ⟨k, hK, hk, heven, hmultiple, hsteps⟩ := hcofinal (max K K0)
  have hk0 : K0 ≤ k := (le_max_right K K0).trans hK
  have hlarge : Real.log 2 ≤ loss * (k : ℝ) := by
    have h0 := (div_lt_iff₀ hloss).mp hK0
    have hle : (K0 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  refine ⟨k, (le_max_left K K0).trans hK, hk, heven, hmultiple, ?_⟩
  intro owner s hi
  obtain ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, hrepair, hlog⟩ := hsteps owner s hi
  refine ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, hrepair, hlog, ?_⟩
  exact mme_log_successor_implies_positive_rate E.copies _ loss k hloss
    (by exact_mod_cast hk) hlarge hlog


#print axioms solution
