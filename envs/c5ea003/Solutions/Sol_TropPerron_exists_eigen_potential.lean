-- Prove2me | solution 1 for TropPerron.exists_eigen_potential
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:18.195669+00:00
-- url     : https://prove2.me/submissions/e85a22ef-ef77-4aaf-b905-595fb2f37493

-- Sol generated from Speculative/AutoResearch/TropicalPerronCore.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TropicalPerronCore
import Theorems.Thm_TropPerron_Wt_sub_le_maxTo

/-!
# Cuninghame-Green construction: the core of the tropical Perron-Frobenius theorem

This file supplies the combinatorial core needed to prove that every finite real
matrix has a max-plus eigenvector (`Speculative.AutoResearch.PerronTheorem`).

The classical construction is carried out here in an elementary, walk-based form:

* `wt M f k` is the weight of the length-`k` walk `f 0 → f 1 → ⋯ → f k`;
* `Wt hn M k i j` is the maximal weight of a length-`k` walk from `i` to `j`
  (defined by the tropical recursion `Wt (k+2) i j = max_l (M i l + Wt (k+1) l j)`);
* `wt_le_Wt` and `exists_wt_eq_Wt` identify `Wt` with the maximum over walks;
* `lam hn M` is the **maximal cycle mean** over closed walks of length at most `n`;
* `wt_splice` removes a closed sub-walk from a walk, and
  `Wt_sub_le_maxTo` (proved by strong induction, using the pigeonhole principle to
  locate a repeated vertex) shows that in the shifted matrix `M - lam` no walk beats
  the best walk of length at most `n`;
* `exists_eigen_potential` then produces the eigenvector: the potential
  `v i = max_{1 ≤ l ≤ n} (Wt l i i₀ - l * lam)`, taken relative to a critical node
  `i₀`, satisfies `max_j (M i j + v j) = lam + v i`.

Nothing here uses `sorry`, `native_decide`, or any new axiom.
-/

open Finset

open TropPerron

variable {n : ℕ}

/-! ### Walks and their weights -/



lemma Wt_one (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Wt hn M 1 i j = M i j := rfl

lemma Wt_succ_succ (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (i j : Fin n) :
    Wt hn M (k + 2) i j =
      Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun l => M i l + Wt hn M (k + 1) l j) := rfl




/-! ### Removing a closed sub-walk -/


/-! ### The maximal cycle mean -/



/-- Closed walks of length at most `n` have nonpositive weight after the shift by
`lam`. -/
lemma Wt_diag_sub_le (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) {d : ℕ}
    (hd : d ∈ Finset.Icc 1 n) (i : Fin n) : Wt hn M d i i - d * lam hn M ≤ 0 := by
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
  have h1 : Wt hn M d i i / d ≤ lam hn M := by
    refine le_trans ?_ (Finset.le_sup'
      (fun k => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => Wt hn M k i i / k)) hd)
    exact Finset.le_sup' (fun i => Wt hn M d i i / d) (Finset.mem_univ i)
  rw [div_le_iff₀ hdpos] at h1
  nlinarith [h1]


/-! ### The eigenvector -/



open TropPerron in
theorem solution(hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : Fin n → ℝ, ∀ i : Fin n,
      Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => M i j + v j)
        = lam hn M + v i := by
  classical
  obtain ⟨k0, hk0mem, hk0⟩ := Finset.exists_mem_eq_sup' (icc_nonempty hn)
    (fun k => Finset.univ.sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun i => Wt hn M k i i / k))
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => Wt hn M k0 i i / k0)
  have hk01 : 1 ≤ k0 := (Finset.mem_Icc.mp hk0mem).1
  have hk0pos : (0:ℝ) < (k0 : ℝ) := by exact_mod_cast hk01
  have hlam : lam hn M = Wt hn M k0 i0 i0 / k0 := by
    rw [lam, hk0, hi0]
  have hcrit : Wt hn M k0 i0 i0 - k0 * lam hn M = 0 := by
    rw [hlam]
    field_simp
    ring
  set v : Fin n → ℝ :=
    fun i => (Finset.Icc 1 n).sup' (icc_nonempty hn)
      (fun l => Wt hn M l i i0 - l * lam hn M) with hv
  have hv0 : v i0 = 0 := by
    refine le_antisymm ?_ ?_
    · exact Finset.sup'_le _ _ fun l hl => Wt_diag_sub_le hn M hl i0
    · rw [hv]
      exact le_trans (le_of_eq hcrit.symm)
        (Finset.le_sup' (fun l => Wt hn M l i0 i0 - l * lam hn M) hk0mem)
  have hupper : ∀ i j : Fin n, M i j + v j ≤ lam hn M + v i := by
    intro i j
    obtain ⟨l, hlmem, hl⟩ := Finset.exists_mem_eq_sup' (icc_nonempty hn)
      (fun l => Wt hn M l j i0 - l * lam hn M)
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hlmem).1
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hvj : v j = Wt hn M (m + 1) j i0 - (m + 1 : ℕ) * lam hn M := by
      rw [hv]; exact hl
    have hstep : M i j + Wt hn M (m + 1) j i0 ≤ Wt hn M (m + 2) i i0 := by
      rw [Wt_succ_succ]
      exact Finset.le_sup' (fun l => M i l + Wt hn M (m + 1) l i0) (Finset.mem_univ j)
    have hred := Wt_sub_le_maxTo hn M i i0 (m + 2) (by omega)
    have hvi : (Finset.Icc 1 n).sup' (icc_nonempty hn)
        (fun l => Wt hn M l i i0 - l * lam hn M) = v i := by rw [hv]
    rw [hvi] at hred
    rw [hvj]
    push_cast at hred ⊢
    linarith
  have hlower : ∀ i : Fin n, ∃ j : Fin n, lam hn M + v i ≤ M i j + v j := by
    intro i
    obtain ⟨l, hlmem, hl⟩ := Finset.exists_mem_eq_sup' (icc_nonempty hn)
      (fun l => Wt hn M l i i0 - l * lam hn M)
    have hl1 : 1 ≤ l := (Finset.mem_Icc.mp hlmem).1
    have hln : l ≤ n := (Finset.mem_Icc.mp hlmem).2
    have hvi : v i = Wt hn M l i i0 - l * lam hn M := by rw [hv]; exact hl
    match l, hl1, hln, hvi with
    | 0, hl1, _, _ => exact absurd hl1 (by omega)
    | 1, _, _, hvi =>
      refine ⟨i0, ?_⟩
      rw [hvi, hv0, Wt_one]
      push_cast
      linarith
    | (m + 2), _, hln, hvi =>
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun j => M i j + Wt hn M (m + 1) j i0)
      refine ⟨j, ?_⟩
      have hwt : Wt hn M (m + 2) i i0 = M i j + Wt hn M (m + 1) j i0 := by
        rw [Wt_succ_succ]; exact hj
      have hvj : Wt hn M (m + 1) j i0 - (m + 1 : ℕ) * lam hn M ≤ v j := by
        rw [hv]
        exact Finset.le_sup' (fun l => Wt hn M l j i0 - l * lam hn M)
          (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hvi, hwt]
      push_cast at hvj ⊢
      linarith
  refine ⟨v, fun i => le_antisymm ?_ ?_⟩
  · exact Finset.sup'_le _ _ fun j _ => hupper i j
  · obtain ⟨j, hj⟩ := hlower i
    exact le_trans hj (Finset.le_sup' (fun j => M i j + v j) (Finset.mem_univ j))
