-- Prove2me | Theorems.Thm_mme_released_interior_simultaneous_parent_matrix_weight_rate
-- name    : mme_released_interior_simultaneous_parent_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:54:09.793913+00:00
-- url     : https://prove2.me/theorems/cd099dc2-aa18-42d0-95fd-5f4220ed7c50
-- title:
--   Common cofinal scales attain the complete interior parent weight
-- statement:
--   For any positive child tolerance, entropy tolerance, copy-rate loss, and replication stride, common cofinal even scales support every released interior recipe. Wherever the regional entropy margin exceeds twice the loss, the actual six-fold parent tensor has positive matrix copies attaining the complete child rates plus six times the parent entropy copy rate. The numerical margin hypothesis is explicit and the final exponent bound remains unproved. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_simultaneous_positive_copy_rate
import Theorems.Thm_mme_released_interior_parent_matrix_weight_log_rate
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed
  MME.CompleteSplit MME.RegionRealization MME.ProfiledCW MME.RecursiveYZ.Certificate
  MME.RecursiveYZ.CWCells MME.RegionRate Filter
open MME.RecursiveYZ.Boundary
universe u

theorem mme_released_interior_simultaneous_parent_matrix_weight_rate
    (delta : ℝ) (hdelta : 0 < delta)
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
            Real.log E.copies) ∧
      let parentRate : ℝ := ((regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
          (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord 2) eps) - 2 * loss) * (k : ℝ)
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
          splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, integerProfile owner s i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      ∀ (tau : ℝ), 0 ≤ tau →
      2 * loss < regionalRate (parent_total s) (regionalSize owner s) (splitCount owner s)
        (integerProfile owner s) - ((∑ r, regionalSize owner s r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteWord 2) eps →
      ∃ (copies : ℕ) (a b d : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj KField (a j) (b j) (d j)))
          (sixSymmetrization (ProfiledCW.tensor KField source)) ∧
        Real.exp (6 * parentRate + ((∑ r, 6 * tau * (((k : ℕ) : ℝ) *
            (((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                    splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := (k / 2) * ((seed owner s).region.getD (e (.inr t)).1.val 0 *
        (splitWeight owner s (e (.inr t)).1 (e (.inr t)).2 +
          splitWeight owner s (e (.inr t)).1 (complement (parent_total s (e (.inr t)).1) (e (.inr t)).2)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == (e (.inr t)).1.val && a.2.1 == sourceShape owner (e (.inr t)).2)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ((4 * N : ℕ) : ℝ) *
        (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
        ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5 ))) ≤
          ∑ j, (((a j * b j * d j : ℕ) : ℝ) ^ tau) := by sorry
