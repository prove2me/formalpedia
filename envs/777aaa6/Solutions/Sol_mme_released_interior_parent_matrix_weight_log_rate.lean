-- Prove2me | solution 1 for mme_released_interior_parent_matrix_weight_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:45:46.876133+00:00
-- url     : https://prove2.me/submissions/b299df07-f43d-40e5-b50c-013f59086984

import Theorems.Thm_mme_released_interior_profiled_output_matrix_weight_rate
import Theorems.Thm_mme_exact_step_six_matrix_weight_log_rate

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open MME.RecursiveYZ.Boundary
open scoped BigOperators
universe u

/-- A positive released interior exact step combines its certified parent
log-copy rate with all boundary and 112 matrix weight rates. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45),
      (seed owner s).boundary = [] →
      ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
        (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
        (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
        (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) ∧
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
          splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2)),
      (∀ r i w, integerProfile owner s i (e (.inl r)) w = (B r).mu (zB r) i w) ∧
      ∀ (n : Fin 6 → ℕ) (reference : Address 4 6 (parent s) n),
      reference ∈ RecursiveXHash.target (fun r c => (2 * k) * splitCount owner s r c) →
      ∀ (L N : ℕ) (positions : Fin L ≃ Position n)
        (length : L * 2 ^ (2 - 1) = N),
      ∀ (P : ProfiledCW.Predicate N) (E : ProfiledCW.ExactStep 2 N P),
      E.output = (fun i x =>
        Graded (parent_total s) i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell (parent_total s) reference)
          (fun cell w => (2 * k) * integerProfile owner s i cell w)
          (ProfiledCW.split positions length x)) →
      0 < E.copies → ∀ (parentRate : ℝ), parentRate ≤ Real.log E.copies →
      ∀ (K : Type u) [Field K] (tau : ℝ), 0 ≤ tau →
      ∃ (copies : ℕ) (a b d : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
          (sixSymmetrization (ProfiledCW.tensor K P)) ∧
        Real.exp (6 * parentRate + ((∑ r, 6 * tau * (((2 * k : ℕ) : ℝ) *
            (((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount owner s (e (.inl r)).1 (e (.inl r)).2 +
                    splitCount owner s (e (.inl r)).1 (complement (parent_total s (e (.inl r)).1) (e (.inl r)).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) + (∑ t,
      let m := k * ((seed owner s).region.getD (e (.inr t)).1.val 0 *
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
          ∑ j, (((a j * b j * d j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [mme_released_interior_profiled_output_matrix_weight_rate.{u}
    delta hdelta] with k hk
  intro owner s hseed
  obtain ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, hweight⟩ := hk owner s hseed
  refine ⟨nB, nI, e, zB, zI, hzB, hzI, B, hmu, ?_⟩
  intro n reference href L N positions length P E houtput hpositive parentRate hparent
    K _ tau htau
  obtain ⟨copies, a, b, d, hcopies, hrestrict, hrate⟩ :=
    hweight n reference href L N positions length K tau htau
  have hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
      (sixSymmetrization (ProfiledCW.tensor K E.output)) := by
    rw [houtput]
    exact hrestrict
  exact mme_exact_step_six_matrix_weight_log_rate E hpositive parentRate hparent
    a b d hcopies tau _ hchild hrate


#print axioms solution
