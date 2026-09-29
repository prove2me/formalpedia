-- Prove2me | solution 1 for mme_released_joint_interior_positive_owner_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:20:47.726995+00:00
-- url     : https://prove2.me/submissions/71aacfee-0ee2-43a0-9116-1009929352d6

import Theorems.Thm_mme_released_interior_weighted_output_matrix_weight_rate
import Theorems.Thm_mme_released_joint_interior_owner_reference_target

open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary
open scoped BigOperators
universe u

/-- Every positive-weight owner reconstructed after joint hashing satisfies
the complete child matrix-weight bound in common source mode order, along one
shared sequence of even scales. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ j : Fin 270, 0 < weight j →
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (ReleasedInterior.parent (component j).2))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
          ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, ReleasedInterior.integerProfile (component j).1 (component j).2 i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      ∀ (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r (2 * k))),
        (∀ r, a r ∈ RecursiveXHash.target (n := size r (2 * k))
          (splitCount r (2 * k))) →
      ∀ (L N : ℕ) (positions : Fin L ≃ Position (fun r => size r (2 * k) j))
        (length : L * 2 ^ (2 - 1) = N),
      ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
      ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
          (sixSymmetrization (ProfiledCW.tensor K (fun i x =>
            Graded (ReleasedInterior.parent_total (component j).2) ((roleEquiv (component j).1).symm i) (fun r t => (splitEquiv r j).symm (a r j t)) (ProfiledCW.split positions length x) ∧
            Useful (fullCell (ReleasedInterior.parent_total (component j).2) (fun r t => (splitEquiv r j).symm (a r j t)))
              (fun cell w => (2 * (k * weight j)) * ReleasedInterior.integerProfile (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) cell w)
              (ProfiledCW.split positions length x)))) ∧
        Real.exp ((∑ r, 6 * tau * (((2 * (k * weight j) : ℕ) : ℝ) *
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
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )) ≤
          ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [mme_released_interior_weighted_output_matrix_weight_rate.{u}
    delta hdelta] with k hk
  intro j hw
  have hseed : (ReleasedInterior.seed (component j).1 (component j).2).boundary = [] := by
    by_contra h
    have hz : weight j = 0 := by simp only [weight, if_neg h]
    omega
  obtain ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, hweight⟩ :=
    hk (weight j) hw (component j).1 (component j).2 hseed
  refine ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, ?_⟩
  intro a ha L N positions length K _ tau htau
  have href : (fun r t => (splitEquiv r j).symm (a r j t)) ∈
      RecursiveXHash.target (n := fun r => size r (2 * k) j)
        (fun r c => (2 * k) * weight j *
          ReleasedInterior.splitCount (component j).1 (component j).2 r c) := by
    apply mme_released_joint_interior_owner_reference_target (2 * k) j a
    assumption
  have href' : (fun r t => (splitEquiv r j).symm (a r j t)) ∈
      RecursiveXHash.target (n := fun r => size r (2 * k) j)
        (fun r c => (2 * (k * weight j)) *
          ReleasedInterior.splitCount (component j).1 (component j).2 r c) := by
    simpa only [Nat.mul_assoc] using href
  exact hweight (fun r => size r (2 * k) j)
    (fun r t => (splitEquiv r j).symm (a r j t)) href'
    L N positions length (roleEquiv (component j).1) K tau htau


#print axioms solution
