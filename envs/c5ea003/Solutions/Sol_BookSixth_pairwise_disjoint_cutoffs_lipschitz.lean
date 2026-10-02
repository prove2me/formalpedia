-- Prove2me | solution 1 for BookSixth.pairwise_disjoint_cutoffs_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T05:54:02.316903+00:00
-- url     : https://prove2.me/submissions/4138c214-fba5-4ae1-8c8a-d1ca1d776b5d

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_lipschitz_cutoff_infred

open scoped BigOperators ENNReal NNReal Topology
open BookSixth Metric

noncomputable section

theorem solution {n : ℕ} (S : Fin n → Set Space3)
    (hS : ∀ i, IsCompact (S i)) (hD : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ (eps : ℝ) (chi : Fin n → Space3 → ℝ), 0 < eps ∧
      (∀ i, LipschitzWith (Real.toNNReal (1 / eps)) (chi i)) ∧
      (∀ i x, x ∈ S i → chi i x = 1) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ S j → chi i x = 0) := by
  classical
  cases n with
  | zero =>
      refine ⟨1, fun _ => 0, by norm_num, fun i => ?_, fun i x => ?_, ?_⟩
      · intro i
        have hz : LipschitzWith (1 : ℝ≥0) (0 : Space3 → ℝ) :=
          LipschitzWith.of_dist_le_mul (fun x y => by simp)
        simpa using hz
      · exact Fin.elim0 i
      · intro i j hij; exact Fin.elim0 i
  | succ n =>
      -- A positive clearance exists for every ordered pair of distinct components.
      have hclr : ∀ i j : Fin (n + 1), i ≠ j → ∃ r : ℝ≥0, 0 < r ∧
          ∀ x ∈ S j, ∀ y ∈ S i, (r : ℝ≥0∞) ≤ edist x y := by
        intro i j hij
        obtain ⟨r, hr0, hr⟩ :=
          Metric.exists_pos_forall_lt_edist (hS j) (hS i).isClosed (hD j i (Ne.symm hij))
        exact ⟨r, hr0, fun x _ y _ => le_of_lt (hr x ‹_› y ‹_›)⟩
      -- The scaled clearance of a pair, as a real; `1 / 3` on the diagonal.
      set rad : (Fin (n + 1) × Fin (n + 1)) → ℝ := fun p =>
        (if h : p.1 = p.2 then (1 : ℝ) else (hclr p.1 p.2 h).choose : ℝ) / 3 with hrad
      have had : ∀ p, 0 < rad p := by
        intro p
        show (0 : ℝ) < (if h : p.1 = p.2 then (1 : ℝ)
          else (hclr p.1 p.2 h).choose : ℝ) / 3
        split
        · norm_num
        · rename_i h; exact div_pos (hclr p.1 p.2 h).choose_spec.1 (by norm_num)
      -- `eps` is the least scaled clearance; a positive, uniform lower bound.
      set eps : ℝ := (Finset.univ : Finset (Fin (n + 1) × Fin (n + 1))).inf'
        Finset.univ_nonempty rad with heps
      have heps0 : 0 < eps := by
        rw [heps]; exact (Finset.lt_inf'_iff _).2 fun p _ => had p
      have hepsrad : ∀ p, eps ≤ rad p := by
        intro p
        rw [heps]; exact Finset.inf'_le _ (Finset.mem_univ p)
      -- Uniform clearance: points of `S j` stay at least `3 * eps` from `S i`.
      have hclear : ∀ i j : Fin (n + 1), i ≠ j → ∀ x : Space3, x ∈ S j →
          ∀ y : Space3, y ∈ S i → ENNReal.ofReal (3 * eps) ≤ edist x y := by
        intro i j hij x hx y hy
        have hval : rad (i, j) = ((hclr i j hij).choose : ℝ) / 3 := by
          rw [hrad]
          show ((if h : (i, j).1 = (i, j).2 then 1 else
            ((hclr (i, j).1 (i, j).2 h).choose : ℝ)) / 3)
              = ((hclr i j hij).choose : ℝ) / 3
          rw [dif_neg hij]
        have h3 : 3 * eps ≤ (hclr i j hij).choose := by
          have hle : eps ≤ ((hclr i j hij).choose : ℝ) / 3 := (hepsrad (i, j)).trans hval.le
          linarith
        have hmain : ENNReal.ofReal (3 * eps) ≤ (hclr i j hij).choose :=
          ENNReal.ofReal_le_coe.mpr h3
        exact hmain.trans ((hclr i j hij).choose_spec.2 x hx y hy)
      -- Cut-offs at radius `eps`, so the Lipschitz constant is exactly `1 / eps`.
      have hget : ∀ i, ∃ f : Space3 → ℝ,
          (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
          (∀ x, x ∈ Metric.cthickening eps (S i) → f x = 1) ∧
          (∀ x, x ∉ Metric.cthickening (2 * eps) (S i) → f x = 0) ∧
          LipschitzWith (Real.toNNReal (1 / eps)) f :=
        fun i => BookSixth.lipschitz_cutoff_infred (K := S i) (hS i) heps0
      choose chi hchi using hget
      refine ⟨eps, chi, heps0, fun i => (hchi i).2.2.2, ?_, ?_⟩
      · intro i x hx
        exact (hchi i).2.1 x (Metric.self_subset_cthickening (S i) hx)
      · intro i j hij x hx
        rcases (S i).eq_empty_or_nonempty with hempty | hne_i
        · refine (hchi i).2.2.1 x ?_
          rw [hempty, Metric.cthickening_empty]
          simp
        · obtain ⟨y, hy, hminy⟩ := IsCompact.exists_infEDist_eq_edist (hS i) hne_i x
          have hmem : ENNReal.ofReal (3 * eps) ≤ infEDist x (S i) := by
            rw [hminy]; exact hclear i j hij x hx y hy
          have hne : x ∉ Metric.cthickening (2 * eps) (S i) := by
            have h2 : (2 * eps : ℝ) < 3 * eps := by linarith [heps0]
            have h3 : (0 : ℝ) < 3 * eps := by linarith [heps0]
            rw [Metric.mem_cthickening_iff, not_le]
            exact (ENNReal.ofReal_lt_ofReal_iff h3).mpr h2 |>.trans_le hmem
          exact (hchi i).2.2.1 x hne

end
