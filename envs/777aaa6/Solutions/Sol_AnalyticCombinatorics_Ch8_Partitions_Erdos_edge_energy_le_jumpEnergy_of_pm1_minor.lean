-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.edge_energy_le_jumpEnergy_of_pm1_minor
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T11:19:13.745698+00:00
-- url     : https://prove2.me/submissions/bf8c378b-87e2-4866-9e2a-351c773d51c5

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_DirichletForm
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_Ellipticity
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Nearest-neighbor ellipticity lower bound (renewal route B, Layer-2 Stage 3c lower)

The lower half of the Dirichlet-form sandwich (ChatGPT ac2 R12 + R13): a `±1` minorization
(`Kc r (r+1) ≥ p`, `Kc (r+1) r ≥ p`) forces the directed jump energy to dominate the nearest-neighbor
edge energy,

  `2p · ∑_r (f(r+1) − f r)² ≤ ∑_{d,e} Kc(d,e)·(f e − f d)²`.

Each undirected edge `(r,r+1)` collects `≥ 2p` from its two directed nearest-neighbor jumps; the two
NN masks are extracted from the full double sum via collapsing inner indicator sums (`sum_eq_single`)
and `sum_filter`.  Combined with `DirichletForm.bounded_jump_energy_le_edge_energy` this gives the full
form sandwich `2p·E_edge ≤ E_K ≤ 3B²·E_edge`.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma edge_left_mem_intVerts {L : ℕ} {r : ℤ} (hr : r ∈ intEdges L) : r ∈ intVerts L := by
  simp only [intEdges, intVerts, Finset.mem_Ico, Finset.mem_Icc] at hr ⊢
  exact ⟨hr.1, le_of_lt hr.2⟩

/-- For `d ∈ [-L,L]`, `d ∈ [-L,L)` iff `d+1 ∈ [-L,L]`. -/
lemma mem_intEdges_iff_right_mem_intVerts {L : ℕ} {d : ℤ} (hd : d ∈ intVerts L) :
    d ∈ intEdges L ↔ d + 1 ∈ intVerts L := by
  simp only [intVerts, intEdges, Finset.mem_Icc, Finset.mem_Ico] at hd ⊢
  constructor
  · intro h; exact ⟨by omega, by omega⟩
  · intro h; exact ⟨by omega, by omega⟩

/-- Collapse the inner sum selecting `e = d+1`. -/
lemma nn_plus_inner_sum_eq
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) {d : ℤ} (hd : d ∈ intVerts L) :
    (∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
      = if d ∈ intEdges L then Kc d (d + 1) * (f (d + 1) - f d) ^ 2 else 0 := by
  classical
  by_cases hdE : d ∈ intEdges L
  · have hd1 : d + 1 ∈ intVerts L := (mem_intEdges_iff_right_mem_intVerts hd).1 hdE
    rw [if_pos hdE]
    calc (∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
          = Kc d (d + 1) * (f (d + 1) - f d) ^ 2 * (if d + 1 = d + 1 then (1 : ℝ) else 0) := by
          refine Finset.sum_eq_single (d + 1) ?_ ?_
          · intro e he hne; rw [if_neg hne, mul_zero]
          · intro hnot; exact False.elim (hnot hd1)
      _ = Kc d (d + 1) * (f (d + 1) - f d) ^ 2 := by simp
  · have hd1not : d + 1 ∉ intVerts L := by
      intro hd1; exact hdE ((mem_intEdges_iff_right_mem_intVerts hd).2 hd1)
    rw [if_neg hdE]
    refine Finset.sum_eq_zero ?_
    intro e he
    by_cases heq : e = d + 1
    · subst e; exact False.elim (hd1not he)
    · rw [if_neg heq, mul_zero]

/-- Collapse the inner sum selecting `d = e+1`. -/
lemma nn_minus_inner_sum_eq
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) {e : ℤ} (he : e ∈ intVerts L) :
    (∑ d ∈ intVerts L, Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
      = if e ∈ intEdges L then Kc (e + 1) e * (f e - f (e + 1)) ^ 2 else 0 := by
  classical
  by_cases heE : e ∈ intEdges L
  · have he1 : e + 1 ∈ intVerts L := (mem_intEdges_iff_right_mem_intVerts he).1 heE
    rw [if_pos heE]
    calc (∑ d ∈ intVerts L, Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
          = Kc (e + 1) e * (f e - f (e + 1)) ^ 2 * (if e + 1 = e + 1 then (1 : ℝ) else 0) := by
          refine Finset.sum_eq_single (e + 1) ?_ ?_
          · intro d hd hne; rw [if_neg hne, mul_zero]
          · intro hnot; exact False.elim (hnot he1)
      _ = Kc (e + 1) e * (f e - f (e + 1)) ^ 2 := by simp
  · have he1not : e + 1 ∉ intVerts L := by
      intro he1; exact heE ((mem_intEdges_iff_right_mem_intVerts he).2 he1)
    rw [if_neg heE]
    refine Finset.sum_eq_zero ?_
    intro d hd
    by_cases hdeq : d = e + 1
    · subst d; exact False.elim (he1not hd)
    · rw [if_neg hdeq, mul_zero]

private lemma filter_mem_intEdges_eq (L : ℕ) :
    (intVerts L).filter (fun d => d ∈ intEdges L) = intEdges L := by
  ext d
  by_cases hdE : d ∈ intEdges L
  · simp [hdE, edge_left_mem_intVerts hdE]
  · simp [hdE]

/-- The `e=d+1` mask evaluates to the forward nearest-neighbor edge sum. -/
lemma nn_plus_mask_sum_eq (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) :
    (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
        Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
      = ∑ r ∈ intEdges L, Kc r (r + 1) * (f (r + 1) - f r) ^ 2 := by
  classical
  calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
          Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
        = ∑ d ∈ intVerts L,
            (if d ∈ intEdges L then Kc d (d + 1) * (f (d + 1) - f d) ^ 2 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact nn_plus_inner_sum_eq Kc f L hd
    _ = ∑ d ∈ (intVerts L).filter (fun d => d ∈ intEdges L),
            Kc d (d + 1) * (f (d + 1) - f d) ^ 2 := by
        symm; rw [Finset.sum_filter]
    _ = ∑ r ∈ intEdges L, Kc r (r + 1) * (f (r + 1) - f r) ^ 2 := by rw [filter_mem_intEdges_eq]

/-- The `d=e+1` mask evaluates to the backward nearest-neighbor edge sum. -/
lemma nn_minus_mask_sum_eq (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) :
    (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
        Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
      = ∑ r ∈ intEdges L, Kc (r + 1) r * (f r - f (r + 1)) ^ 2 := by
  classical
  calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
          Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
        = ∑ e ∈ intVerts L, ∑ d ∈ intVerts L,
            Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0) := by rw [Finset.sum_comm]
    _ = ∑ e ∈ intVerts L,
            (if e ∈ intEdges L then Kc (e + 1) e * (f e - f (e + 1)) ^ 2 else 0) := by
        refine Finset.sum_congr rfl ?_
        intro e he
        exact nn_minus_inner_sum_eq Kc f L he
    _ = ∑ e ∈ (intVerts L).filter (fun e => e ∈ intEdges L),
            Kc (e + 1) e * (f e - f (e + 1)) ^ 2 := by
        symm; rw [Finset.sum_filter]
    _ = ∑ r ∈ intEdges L, Kc (r + 1) r * (f r - f (r + 1)) ^ 2 := by rw [filter_mem_intEdges_eq]

/-- The two nearest-neighbor directed contributions are bounded by the full directed jump energy. -/
lemma two_nn_edge_terms_le_full_jumpEnergy
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) (hKnn : ∀ d e, 0 ≤ Kc d e) :
    (∑ r ∈ intEdges L,
        (Kc r (r + 1) * (f (r + 1) - f r) ^ 2 + Kc (r + 1) r * (f r - f (r + 1)) ^ 2))
      ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := by
  classical
  have hmask_le_full :
      (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
          Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
        + (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
          Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
        ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := by
    calc (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
          + (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0))
          = ∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
              (Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0)
                + Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [← Finset.sum_add_distrib]
      _ ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro d hd
          refine Finset.sum_le_sum ?_
          intro e he
          have hterm_nonneg : 0 ≤ Kc d e * (f e - f d) ^ 2 := mul_nonneg (hKnn d e) (sq_nonneg _)
          by_cases hp : e = d + 1
          · by_cases hm : d = e + 1
            · omega
            · rw [if_pos hp, if_neg hm]; simpa using hterm_nonneg
          · by_cases hm : d = e + 1
            · rw [if_neg hp, if_pos hm]; simpa using hterm_nonneg
            · rw [if_neg hp, if_neg hm]; simpa using hterm_nonneg
  calc (∑ r ∈ intEdges L,
        (Kc r (r + 1) * (f (r + 1) - f r) ^ 2 + Kc (r + 1) r * (f r - f (r + 1)) ^ 2))
        = (∑ r ∈ intEdges L, Kc r (r + 1) * (f (r + 1) - f r) ^ 2)
          + (∑ r ∈ intEdges L, Kc (r + 1) r * (f r - f (r + 1)) ^ 2) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * (f e - f d) ^ 2 * (if e = d + 1 then (1 : ℝ) else 0))
          + (∑ d ∈ intVerts L, ∑ e ∈ intVerts L,
            Kc d e * (f e - f d) ^ 2 * (if d = e + 1 then (1 : ℝ) else 0)) := by
        rw [nn_plus_mask_sum_eq, nn_minus_mask_sum_eq]
    _ ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := hmask_le_full

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Finset
theorem solution
    (Kc : ℤ → ℤ → ℝ) (f : ℤ → ℝ) (L : ℕ) (p : ℝ)
    (hpnn : 0 ≤ p) (hKnn : ∀ d e, 0 ≤ Kc d e)
    (hplus : ∀ r ∈ intEdges L, p ≤ Kc r (r + 1))
    (hminus : ∀ r ∈ intEdges L, p ≤ Kc (r + 1) r) :
    2 * p * edgeEnergyInt L f
      ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 := by
  classical
  have hpair :
      ∀ r ∈ intEdges L,
        2 * p * edgeSq f r
          ≤ Kc r (r + 1) * (f (r + 1) - f r) ^ 2 + Kc (r + 1) r * (f r - f (r + 1)) ^ 2 := by
    intro r hr
    have hsq : (f r - f (r + 1)) ^ 2 = (f (r + 1) - f r) ^ 2 := by ring
    rw [hsq, edgeSq]
    have hnon : 0 ≤ (f (r + 1) - f r) ^ 2 := sq_nonneg _
    calc 2 * p * (f (r + 1) - f r) ^ 2 = (p + p) * (f (r + 1) - f r) ^ 2 := by ring
      _ ≤ (Kc r (r + 1) + Kc (r + 1) r) * (f (r + 1) - f r) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hplus r hr, hminus r hr]) hnon
      _ = Kc r (r + 1) * (f (r + 1) - f r) ^ 2 + Kc (r + 1) r * (f (r + 1) - f r) ^ 2 := by ring
  calc 2 * p * edgeEnergyInt L f
        = ∑ r ∈ intEdges L, 2 * p * edgeSq f r := by
        unfold edgeEnergyInt; rw [Finset.mul_sum]
    _ ≤ ∑ r ∈ intEdges L,
          (Kc r (r + 1) * (f (r + 1) - f r) ^ 2 + Kc (r + 1) r * (f r - f (r + 1)) ^ 2) :=
        Finset.sum_le_sum hpair
    _ ≤ ∑ d ∈ intVerts L, ∑ e ∈ intVerts L, Kc d e * (f e - f d) ^ 2 :=
        two_nn_edge_terms_le_full_jumpEnergy Kc f L hKnn
