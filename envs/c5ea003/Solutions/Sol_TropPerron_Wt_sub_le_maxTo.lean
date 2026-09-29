-- Prove2me | solution 1 for TropPerron.Wt_sub_le_maxTo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:24:23.324529+00:00
-- url     : https://prove2.me/submissions/93e75e20-4a22-48e6-a14e-44b97387a6e6

-- Sol generated from Speculative/AutoResearch/TropicalPerronCore.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_TropicalPerronCore
import Theorems.Thm_TropPerron_exists_wt_eq_Wt
import Theorems.Thm_TropPerron_wt_le_Wt
import Theorems.Thm_TropPerron_wt_splice

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
theorem solution(hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ∀ k : ℕ, 1 ≤ k →
      Wt hn M k i j - k * lam hn M ≤
        (Finset.Icc 1 n).sup' (icc_nonempty hn) (fun l => Wt hn M l i j - l * lam hn M) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1
    by_cases hkn : k ≤ n
    · exact Finset.le_sup' (fun l => Wt hn M l i j - l * lam hn M)
        (Finset.mem_Icc.mpr ⟨hk1, hkn⟩)
    · push_neg at hkn
      obtain ⟨f, hf0, hfk, hfw⟩ := exists_wt_eq_Wt hn M k hk1 i j
      have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
      obtain ⟨x, y, hxy, hfxy⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt (fun t : Fin (n + 1) => f t) hcard
      have hne' : (x : ℕ) ≠ (y : ℕ) := fun hxyval => hxy (Fin.ext hxyval)
      have hxle : (x : ℕ) ≤ n := Nat.lt_succ_iff.mp x.isLt
      have hyle : (y : ℕ) ≤ n := Nat.lt_succ_iff.mp y.isLt
      have hfx : f (x : ℕ) = f (y : ℕ) := hfxy
      obtain ⟨a, b, hab, hbn, heq⟩ : ∃ a b : ℕ, a < b ∧ b ≤ n ∧ f a = f b := by
        rcases lt_or_gt_of_ne hne' with hlt | hgt
        · exact ⟨(x : ℕ), (y : ℕ), hlt, hyle, hfx⟩
        · exact ⟨(y : ℕ), (x : ℕ), hgt, hxle, hfx.symm⟩
      set d := b - a with hd
      have hd1 : 1 ≤ d := by omega
      have hdn : d ≤ n := by omega
      have hbk : b ≤ k := by omega
      have hsp := wt_splice M f hab hbk heq
      rw [← hd] at hsp
      -- the excised closed sub-walk has nonpositive shifted weight
      have hAA : f (a + d) = f a := by
        rw [show a + d = b by omega]; exact heq.symm
      have hclosed : wt M (fun t => f (a + t)) d ≤ d * lam hn M := by
        have hle := wt_le_Wt hn M d hd1 (fun t => f (a + t))
        simp only [Nat.add_zero, hAA] at hle
        have h2 := Wt_diag_sub_le hn M (Finset.mem_Icc.mpr ⟨hd1, hdn⟩) (f a)
        linarith
      -- the shortened walk still runs from `i` to `j`
      have hstart : (if (0:ℕ) < a then f 0 else f (0 + d)) = i := by
        by_cases h0 : 0 < a
        · rw [if_pos h0]; exact hf0
        · rw [if_neg (by omega), show (0:ℕ) + d = b by omega, ← heq, show a = 0 by omega]
          exact hf0
      have hend : (if k - d < a then f (k - d) else f (k - d + d)) = j := by
        rw [if_neg (by omega), show k - d + d = k by omega]; exact hfk
      have hgle := wt_le_Wt hn M (k - d) (by omega) (fun t => if t < a then f t else f (t + d))
      simp only [hstart, hend] at hgle
      have hIH := ih (k - d) (by omega) (by omega)
      have hcast : ((k - d : ℕ) : ℝ) = (k : ℝ) - (d : ℝ) := by
        have : d ≤ k := by omega
        push_cast [this]
        ring
      rw [hcast] at hIH
      rw [← hfw]
      rw [hsp]
      linarith
