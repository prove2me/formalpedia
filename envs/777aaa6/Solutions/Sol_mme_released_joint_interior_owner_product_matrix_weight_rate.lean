-- Prove2me | solution 1 for mme_released_joint_interior_owner_product_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:50:42.358986+00:00
-- url     : https://prove2.me/submissions/e326d257-5140-49a1-b23d-fe650b829d85

import Theorems.Thm_mme_released_joint_interior_positive_owner_matrix_weight_rate
import Theorems.Thm_mme_released_joint_interior_zero_owner_output
import Theorems.Thm_mme_six_product_exponential_extraction

open MME MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.ReleasedJointInterior MME.RecursiveYZ.Boundary
open scoped BigOperators
universe u

/-- All 270 owner outputs combine with the sum of their complete child rates.
Positive owners retain the boundary and interior formula certificates; empty
owners contribute rate zero. The rates are uniform over joint target addresses. -/
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
      ∀ (L N : Fin 270 → ℕ)
        (positions : ∀ j, Fin (L j) ≃ Position (fun r => size r (2 * k) j))
        (length : ∀ j, L j * 2 ^ (2 - 1) = N j),
      let O : ∀ j, ProfiledCW.Predicate (N j) := fun j i x =>
        Graded (ReleasedInterior.parent_total (component j).2)
          ((roleEquiv (component j).1).symm i)
          (fun r t => (splitEquiv r j).symm (a r j t))
          (ProfiledCW.split (positions j) (length j) x) ∧
        Useful (fullCell (ReleasedInterior.parent_total (component j).2)
          (fun r t => (splitEquiv r j).symm (a r j t)))
          (fun c w => (2 * k) * weight j * ReleasedInterior.integerProfile
            (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
          (ProfiledCW.split (positions j) (length j) x)
      ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (rows j) (cols j) (inner j)))
          (sixSymmetrization (TensorObj.kronFin 270
            (fun j => ProfiledCW.tensor K (O j)))) ∧
        Real.exp (∑ j, rate j) ≤
          ∑ j, (((rows j * cols j * inner j : ℕ) : ℝ) ^ tau) := by
  classical
  filter_upwards [mme_released_joint_interior_positive_owner_matrix_weight_rate.{u}
    delta hdelta] with k hk
  intro K _ tau htau
  let Certificate (j : Fin 270) (rate : ℝ) : Prop :=
    (weight j = 0 → rate = 0) ∧ (0 < weight j →
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (ReleasedInterior.parent (component j).2))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (e (.inl r)).2 +
          ReleasedInterior.splitCount (component j).1 (component j).2 (e (.inl r)).1 (complement (ReleasedInterior.parent_total (component j).2 (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, ReleasedInterior.integerProfile (component j).1 (component j).2 i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      rate = (∑ r, 6 * tau * (((2 * (k * weight j) : ℕ) : ℝ) *
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
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 ))
  let Extract (j : Fin 270) (rate : ℝ) : Prop :=
    ∀ (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r (2 * k))),
      (∀ r, a r ∈ RecursiveXHash.target (n := size r (2 * k))
        (splitCount r (2 * k))) →
    ∀ (L N : ℕ) (positions : Fin L ≃ Position (fun r => size r (2 * k) j))
      (length : L * 2 ^ (2 - 1) = N),
    ∃ (copies : ℕ) (rows cols inner : Fin copies → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun t => MMObj K (rows t) (cols t) (inner t)))
        (sixSymmetrization (ProfiledCW.tensor K (fun i x =>
          Graded (ReleasedInterior.parent_total (component j).2)
            ((roleEquiv (component j).1).symm i)
            (fun r t => (splitEquiv r j).symm (a r j t))
            (ProfiledCW.split positions length x) ∧
          Useful (fullCell (ReleasedInterior.parent_total (component j).2)
            (fun r t => (splitEquiv r j).symm (a r j t)))
            (fun c w => (2 * k) * weight j * ReleasedInterior.integerProfile
              (component j).1 (component j).2 ((roleEquiv (component j).1).symm i) c w)
            (ProfiledCW.split positions length x)))) ∧
      Real.exp rate ≤ ∑ t, (((rows t * cols t * inner t : ℕ) : ℝ) ^ tau)
  have hex : ∀ j, ∃ rate, Certificate j rate ∧ Extract j rate := by
    intro j
    by_cases hw : 0 < weight j
    · obtain ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, hbound⟩ := hk j hw
      let rate : ℝ := (∑ r, 6 * tau * (((2 * (k * weight j) : ℕ) : ℝ) *
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
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 )
      refine ⟨rate, ⟨?_, ?_⟩, ?_⟩
      · intro hz
        omega
      · intro _
        exact ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, rfl⟩
      · intro a ha L N positions length
        obtain ⟨q, rows, cols, inner, _, hr, hb⟩ :=
          hbound a (by assumption) L N positions length K tau htau
        refine ⟨q, rows, cols, inner, ?_, hb⟩
        simpa only [Nat.mul_assoc] using hr
    · have hz : weight j = 0 := by omega
      refine ⟨0, ⟨fun _ => rfl, fun h => (hw h).elim⟩, ?_⟩
      intro a _ L N positions length
      have hr := mme_released_joint_interior_zero_owner_output
        (K := K) (2 * k) j hz a positions length (roleEquiv (component j).1)
      refine ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, ?_, ?_⟩
      · simpa only [TensorObj.bigAdd, Fin.sum_univ_one] using hr
      · simp
  choose rate hcert hextract using hex
  refine ⟨rate, fun j => (hcert j).1, fun j => (hcert j).2, ?_⟩
  intro a ha L N positions length O
  apply mme_six_product_exponential_extraction
    (fun j => ProfiledCW.tensor K (O j)) tau rate
  intro j
  exact hextract j a (by assumption) (L j) (N j) (positions j) (length j)


#print axioms solution
