-- Prove2me | solution 1 for mme_released_interior_112_all_cells_six_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:41:07.638082+00:00
-- url     : https://prove2.me/submissions/cf63d212-7d19-4dc1-9195-077e6e67bd8d

import Theorems.Thm_mme_released_interior_112_all_cells_physical_entropy_rate

open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit Filter
open scoped BigOperators
universe u

/-- The entropy and exact matrix volumes give the full matrix weight of
all released 112 children, including empty cells, at one common threshold. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (owner : Fin 6) (s : Fin 45) (r : Fin 6)
      (c : Split s) (z : Fin 3),
      (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
      let m := k * ((seed owner s).region.getD r.val 0 *
        (splitWeight owner s r c +
          splitWeight owner s r (complement (parent_total s r) c)) * denominator)
      let N := denominator * m
      let L := (2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * ((((seed owner s).children.find?
        (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2)) * m
      let p : ℝ :=
        (((((seed owner s).children.find?
          (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD
            (0, [], 0)).2.2) : ℝ) / denominator
      ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b d : Fin copies → ℕ),
        0 < copies ∧
        TensorObj.Restrict (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (d j)))
          (sixSymmetrization
            (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount owner s r c +
                splitCount owner s r (complement (parent_total s r) c))) (Equiv.refl _)
              (fun _ => Unit.unit) (fun _ i => (c.val i).val)
              (fun i _ w => (2 * k) * integerProfile owner s i ⟨r, c⟩ w))) ∧
        (∀ j, a j * b j * d j = 5 ^ (6 * (4 * G + 2 * L))) ∧
        ∀ tau : ℝ,
          Real.exp (((4 * N : ℕ) : ℝ) *
            (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
              ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5) ≤
                ∑ j, (((a j * b j * d j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [mme_released_interior_112_all_cells_physical_entropy_rate
    delta hdelta] with k hk
  intro owner s r c z hshape
  dsimp only
  intro K _
  obtain ⟨copies, a, b, d, hcopies, hrestrict, hvolume, hlog⟩ :=
    hk owner s r c z hshape K
  refine ⟨copies, a, b, d, hcopies, hrestrict, hvolume, ?_⟩
  intro tau
  have hcr : (0 : ℝ) < copies := by exact_mod_cast hcopies
  have hcount := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hcr] at hcount
  simp_rw [hvolume]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hweight (e : ℕ) :
      (((5 ^ e : ℕ) : ℝ) ^ tau) = Real.exp ((e : ℝ) * tau * Real.log 5) := by
    rw [Nat.cast_pow, Real.rpow_def_of_pos (by positivity), Real.log_pow]
    simp only [Nat.cast_ofNat]
    congr 1
    ring
  rw [Real.exp_add, ← hweight]
  exact mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg (by positivity) _)


#print axioms solution
