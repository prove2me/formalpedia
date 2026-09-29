-- Prove2me | solution 1 for mme_released_interior_simultaneous_coordinate_repair_restriction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:48:28.332334+00:00
-- url     : https://prove2.me/submissions/c4d99d1f-7b08-433c-8587-a91649ad7a79

import Theorems.Thm_mme_released_interior_simultaneous_uniform_repair_restriction
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
universe u

/-- Every graded profile is a subset of the complete-word functions on its
positions, so three mode profiles have at most the unrestricted triple count. -/
private theorem mme_profile_capacity_le_unrestricted
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
  have h (i : Fin 3) : Nat.card (Block ell cell shape mu i) ≤
      (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P := by
    have h := Nat.card_le_card_of_injective
      (fun f : Block ell cell shape mu i => f.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h
  calc
    _ ≤ ∏ _ : Fin 3, (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => h i)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

/-- The logarithm of the repair capacity is bounded linearly in the number
of fine-word coordinates, independently of the specific profiles. -/
private theorem mme_profile_capacity_log_le_fine_length
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) ≤
      (3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3 := by
  let cap := ∏ i : Fin 3, Nat.card (Block ell cell shape mu i)
  by_cases hc : cap = 0
  · change Real.log (cap : ℝ) ≤ _
    rw [hc, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · have hpos : (0 : ℝ) < cap := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hbound : (cap : ℝ) ≤ (3 : ℝ) ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
      exact_mod_cast mme_profile_capacity_le_unrestricted ell cell shape mu
    have h := Real.log_le_log hpos hbound
    rw [Real.log_pow] at h
    exact h


/-- One repair base gives arbitrarily small repair loss per physical fine
coordinate, uniformly over all interior recipes and cofinal replication scales. -/
theorem solution
    (stride : ℕ) (hstride : 0 < stride)
    {KField : Type u} [Field KField] (eta : ℝ) (heta : 0 < eta) (eps : ℝ) (heps : 0 < eps) :
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
          eta * (4 * (k * denominator ^ 4) : ℕ) := by
  classical
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 3 * Real.log 3 := mul_pos (by norm_num) h3
  obtain ⟨d, hd, hscales⟩ :=
    mme_released_interior_simultaneous_uniform_repair_restriction
      stride hstride (KField := KField) (eta / (3 * Real.log 3))
      (div_pos heta hden) eps heps
  refine ⟨d, hd, ?_⟩
  intro K
  obtain ⟨k, hK, hk, heven, hmultiple, hsteps⟩ := hscales K
  refine ⟨k, hK, hk, heven, hmultiple, ?_⟩
  intro owner s hi
  obtain ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, hrepair⟩ := hsteps owner s hi
  refine ⟨positions, reference, href, E, hcount, hexponent, houtput, hrestrict,
    hcopies, ?_⟩
  have hcap := mme_profile_capacity_log_le_fine_length 2
    (fullCell (parent_total s) reference) (fun c i => (c.2.val i).val)
    (fun i c w => k * integerProfile owner s i c w)
  have hpositions := Fintype.card_congr positions
  simp only [Fintype.card_fin] at hpositions
  have hlength : Fintype.card (Position (fun r : Fin 6 => k * regionalSize owner s r)) *
      2 ^ (2 - 1) = 4 * (k * denominator ^ 4) := by
    rw [← hpositions]
    ring
  rw [hlength] at hcap
  have hrepair' : Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤ Real.log 8 +
      (eta / (3 * Real.log 3)) *
      Real.log ((∏ i : Fin 3, Nat.card (Block 2 (fullCell (parent_total s) reference)
        (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile owner s i c w) i)) : ℕ) := by
    simpa only [Nat.cast_prod] using hrepair
  calc
    _ ≤ _ := hrepair'
    _ ≤ Real.log 8 + (eta / (3 * Real.log 3)) *
        ((3 * (4 * (k * denominator ^ 4)) : ℕ) * Real.log 3) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcap (div_pos heta hden).le)
    _ = _ := by
      push_cast
      field_simp


#print axioms solution
