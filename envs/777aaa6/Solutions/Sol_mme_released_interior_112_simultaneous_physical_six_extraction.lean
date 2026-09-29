-- Prove2me | solution 1 for mme_released_interior_112_simultaneous_physical_six_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:09:31.843659+00:00
-- url     : https://prove2.me/submissions/2693d0e3-556f-416e-bce1-9ea75be4c914

import Theorems.Thm_mme_released_interior_112_scaled_physical_six_extraction
import Mathlib.Tactic.Choose

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
universe u

private theorem conditional_extraction
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in atTop,
      (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
      (0 < (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c))) →
      let m := k * ((seed owner s).region.getD r.val 0 *
        (splitWeight owner s r c +
          splitWeight owner s r (complement (parent_total s r) c)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
        0 < A ∧ H ≤ 4 ^ N ∧
        ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
        (Nat.choose (2 * N) N : ℝ) *
          Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ 4 * (A : ℝ) * (H : ℝ) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b d : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount owner s r c +
                  splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ i => (c.val i).val)
                (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) ∧
          ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤ (copies : ℝ) ∧
          ∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L)) := by
  by_cases hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1
  · by_cases hweight : 0 < (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c))
    · obtain ⟨C, hC, h⟩ :=
        mme_released_interior_112_scaled_physical_six_extraction
          owner s r c z hshape hweight
      exact ⟨C, hC, h.mono (fun _ hk _ _ => hk)⟩
    · refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
      intro k _ hp
      exact (hweight hp).elim
  · refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
    intro k hs _
    exact (hshape hs).elim

/-- Fixed loss constants and a single cofinal physical replication scale
support every positively weighted released 112 cell simultaneously. -/
theorem solution :
    ∃ C : Fin 6 → (s : Fin 45) → Fin 6 → Split s → Fin 3 → ℝ,
      (∀ owner s r c z, 0 ≤ C owner s r c z) ∧
      ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45) (r : Fin 6)
        (c : Split s) (z : Fin 3),
      (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
      (0 < (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c))) →
      let m := k * ((seed owner s).region.getD r.val 0 *
        (splitWeight owner s r c +
          splitWeight owner s r (complement (parent_total s r) c)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
        0 < A ∧ H ≤ 4 ^ N ∧
        ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          Real.exp (-(C owner s r c z) * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
        (Nat.choose (2 * N) N : ℝ) *
          Real.exp (-2 * (C owner s r c z) * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ 4 * (A : ℝ) * (H : ℝ) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b d : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount owner s r c +
                  splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ i => (c.val i).val)
                (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) ∧
          ((A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
            Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))))) ^ 2 ≤ (copies : ℝ) ∧
          ∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L)) := by
  classical
  choose C hC h using conditional_extraction.{u}
  refine ⟨C, hC, ?_⟩
  exact eventually_all.mpr (fun owner =>
    eventually_all.mpr (fun s =>
      eventually_all.mpr (fun r =>
        eventually_all.mpr (fun c => eventually_all.mpr (fun z => h owner s r c z)))))


#print axioms solution
