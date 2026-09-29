-- Prove2me | solution 1 for mme_released_interior_simultaneous_cofinal_graded_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:27:28.104518+00:00
-- url     : https://prove2.me/submissions/340ddf3f-62a3-42db-8840-0ba99431b0ae

import Theorems.Thm_mme_released_interior_graded_histogram_exact_step_with_repair_scale
import Definitions.Def_mme_released_interior_integer_profiles
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

private theorem mme_interior_arbitrarily_large_size_test
    (stride : ℕ) (hstride : 0 < stride)
    (d : ℕ) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
      (8 * d : ℝ) * (25 * 6 *
        (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * eps ^ 2 := by
  let B : ℝ := (8 * d : ℝ) * (25 * 6 *
    (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2)
  have hfactor : 0 < (denominator : ℝ) ^ 2 * eps ^ 2 := by
    exact mul_pos (by norm_num [denominator]) (sq_pos_of_pos heps)
  obtain ⟨j, hj⟩ := exists_nat_gt (B / ((denominator : ℝ) ^ 2 * eps ^ 2))
  let k := 2 * (stride * max K (j + 1))
  have hlarge : max K (j + 1) ≤ k := by
    have hs : 1 ≤ stride := hstride
    have hm := Nat.mul_le_mul_right (max K (j + 1)) hs
    simp only [one_mul] at hm
    dsimp [k]
    omega
  have hK : K ≤ k := (le_max_left K (j + 1)).trans hlarge
  have hjk : j < k := (Nat.lt_succ_self j).trans_le
    ((le_max_right K (j + 1)).trans hlarge)
  have heven : Even k := ⟨stride * max K (j + 1), by dsimp [k]; omega⟩
  have hmultiple : stride ∣ k := ⟨2 * max K (j + 1), by dsimp [k]; ring⟩
  have hkr : (j : ℝ) < k := by exact_mod_cast hjk
  have hB : B < (k : ℝ) * ((denominator : ℝ) ^ 2 * eps ^ 2) :=
    (div_lt_iff₀ hfactor).mp (hj.trans hkr)
  refine ⟨k, hK, lt_of_le_of_lt (Nat.zero_le j) hjk, heven, hmultiple, ?_⟩
  simpa only [B, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hB.le


/-- A common arbitrarily large replication scale works for every released interior
recipe. The individual extraction steps retain their own exact counts and repair
budgets; this does not yet combine their tensor restrictions. -/
theorem solution
    (stride : ℕ) (hstride : 0 < stride)
    (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
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
        E.output = fun i x => Graded (parent_total s) i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell (parent_total s) reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x)  := by
  obtain ⟨k, hK, hk, heven, hmultiple, hscale⟩ :=
    mme_interior_arbitrarily_large_size_test stride hstride d eps heps K
  refine ⟨k, hK, hk, heven, hmultiple, ?_⟩
  intro owner s hi
  exact mme_released_interior_graded_histogram_exact_step_with_repair_scale
    owner s hi d hd k hk eps heps hscale


#print axioms solution
