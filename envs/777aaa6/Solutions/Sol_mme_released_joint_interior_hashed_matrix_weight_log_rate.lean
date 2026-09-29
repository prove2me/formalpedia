-- Prove2me | solution 1 for mme_released_joint_interior_hashed_matrix_weight_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:32:46.710983+00:00
-- url     : https://prove2.me/submissions/000b34dd-6b67-43fc-b0d4-5b181ba925e0

import Theorems.Thm_mme_released_joint_interior_owner_product_matrix_weight_rate
import Theorems.Thm_mme_released_joint_interior_hashed_owner_output_restrict
import Theorems.Thm_mme_repeated_extraction_six_matrix_weight_rate

open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary
open scoped BigOperators
universe u

/-- Joint hashing contributes its exact post-repair multiplicity to the full
certified child rate. All 270 owners remain in the source window product. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
    ∃ rate : Fin 270 → ℝ,
      (∀ j, weight j = 0 → rate j = 0) ∧
      (∀ j, 0 < weight j →
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (ReleasedInterior.parent (component j).2))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
          ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, ReleasedInterior.integerProfile (component j).1 (component j).2 i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      rate j = (∑ r, 6 * tau * (((2 * (k * weight j) : ℕ) : ℝ) *
            (((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
                    ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := (k * weight j) * ((ReleasedInterior.seed (component j).1 (component j).2).region.getD (e (.inr t)).1.val 0 *
        (ReleasedInterior.splitWeight (component j).1 (component j).2 (e (.inr t)).1 (e (.inr t)).2 +
          ReleasedInterior.splitWeight (component j).1 (component j).2 (e (.inr t)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inr t)).1) (e (.inr t)).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((ReleasedInterior.seed (component j).1 (component j).2).children.find?
          (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == ReleasedInterior.sourceShape (component j).1 (e (.inr t)).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )) ∧
      ∀ (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r (2 * k))),
        (∀ r, a r ∈ RecursiveXHash.target (n := size r (2 * k))
          (splitCount r (2 * k))) →
      ∀ (eps : ℝ)
    (E : ∀ r : Fin 6, ProfiledCW.ExactStep 2 (blocks r (2 * k) * 4) (gradedSource r (2 * k) eps))
    (_houtput : ∀ r, (E r).output = fun i x =>
      Graded (parent_total r) i (a r)
        (ProfiledCW.split (positions r (2 * k)) (positions_length r (2 * k)) x) ∧
      Useful (fullCell (parent_total r) (a r)) (integerProfile r (2 * k) i)
        (ProfiledCW.split (positions r (2 * k)) (positions_length r (2 * k)) x))
    (_e : ∀ j : Fin 270, Fin (((2 * k) * weight j * denominator ^ 4) * 2) ≃
      Position (fun r => size r (2 * k) j))
    (_length : ∀ j : Fin 270,
      (((2 * k) * weight j * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
        ((2 * k) * weight j * denominator ^ 4) * 4)
    (_hp : 0 < ∏ r, (E r).copies),
    let P : ∀ j : Fin 270,
        ProfiledCW.Predicate (((2 * k) * weight j * denominator ^ 4) * 4) :=
      fun j i z => 0 < weight j →
        (∀ p : Fin ((2 * k) * weight j * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p q).val) =
            ReleasedInterior.parent (component j).2 0 ((roleEquiv (component j).1).symm i)) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin ((2 * k) * weight j * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl _) rfl z p = w} : ℝ) /
              ((2 * k) * weight j * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows (component j).1 (component j).2).map
              (fun p => if ReleasedGlobal.atom p.1
                ((roleEquiv (component j).1).symm i) = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps
    ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ), 0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
        (sixSymmetrization (TensorObj.kronFin 270
          (fun j => ProfiledCW.tensor K (P j)))) ∧
      Real.exp (6 * Real.log ((∏ r, (E r).copies : ℕ) : ℝ) + ∑ j, rate j) ≤
        ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [mme_released_joint_interior_owner_product_matrix_weight_rate.{u}
    delta hdelta, eventually_ge_atTop 1] with k hk hkpos
  intro K _ tau htau
  obtain ⟨rate, hzero, hcert, hchild⟩ := hk K tau htau
  refine ⟨rate, hzero, hcert, ?_⟩
  intro a ha eps E houtput e length hp P
  clear hk hzero hcert
  unfold RecursiveXHash.target at ha
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
  obtain ⟨q, rows, cols, inner, hq, hr, hb⟩ :=
    hchild a (by
      unfold RecursiveXHash.target
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha)
      (fun j => ((2 * k) * weight j * denominator ^ 4) * 2)
      (fun j => ((2 * k) * weight j * denominator ^ 4) * 4) e length
  have hparent := mme_released_joint_interior_hashed_owner_output_restrict
    (K := K) (2 * k) (by omega) eps E a houtput e length
  apply mme_repeated_extraction_six_matrix_weight_rate rows cols inner hq tau
    (Real.log ((∏ r, (E r).copies : ℕ) : ℝ)) (∑ j, rate j) hparent ?_ hr hb
  exact (Real.exp_log (Nat.cast_pos.mpr hp)).le


#print axioms solution
