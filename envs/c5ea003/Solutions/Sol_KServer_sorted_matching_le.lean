-- Prove2me | solution 1 for KServer.sorted_matching_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T04:17:46.671141+00:00
-- url     : https://prove2.me/submissions/16be7223-7669-41b1-84d3-316cc72c3340

import Mathlib

/-- The four-point inequality on a line: an uncrossed pairing is never longer than a
crossed one. -/
private theorem four_point {a a' b b' : ℝ} (ha : a ≤ a') (hb : b ≤ b') :
    |a - b| + |a' - b'| ≤ |a - b'| + |a' - b| := by
  have h3 : a - b' ≤ |a - b'| := le_abs_self _
  have h4 : b' - a ≤ |a - b'| := by rw [abs_sub_comm]; exact le_abs_self _
  have h5 : a' - b ≤ |a' - b| := le_abs_self _
  have h6 : b - a' ≤ |a' - b| := by rw [abs_sub_comm]; exact le_abs_self _
  rcases le_total a b with h1 | h1 <;> rcases le_total a' b' with h2 | h2
  · rw [abs_of_nonpos (by linarith : a - b ≤ 0), abs_of_nonpos (by linarith : a' - b' ≤ 0)]
    linarith
  · rw [abs_of_nonpos (by linarith : a - b ≤ 0), abs_of_nonneg (by linarith : 0 ≤ a' - b')]
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_of_nonpos (by linarith : a' - b' ≤ 0)]
    linarith
  · rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_of_nonneg (by linarith : 0 ≤ a' - b')]
    linarith

/-- For two monotone tuples, pairing them in order is at least as cheap as pairing them
through any permutation.  Induction on the size of the permutation's support: the largest
misplaced index can always be put back, by the four-point inequality. -/
private theorem sorted_le_perm_aux {k : ℕ} (a b : Fin k → ℝ) (ha : Monotone a)
    (hb : Monotone b) :
    ∀ n : ℕ, ∀ π : Equiv.Perm (Fin k),
      (Finset.univ.filter (fun i => π i ≠ i)).card ≤ n →
      ∑ i, |a i - b i| ≤ ∑ i, |a i - b (π i)| := by
  classical
  intro n
  induction n with
  | zero =>
    intro π hπ
    have hfix : ∀ i, π i = i := by
      intro i
      by_contra hc
      have hmem : i ∈ Finset.univ.filter (fun i => π i ≠ i) := by simp [hc]
      have := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    simp only [hfix]
    exact le_rfl
  | succ n ih =>
    intro π hπ
    by_cases hid : ∀ i, π i = i
    · simp only [hid]
      exact le_rfl
    · rw [not_forall] at hid
      obtain ⟨i₀, hi₀⟩ := hid
      set S : Finset (Fin k) := Finset.univ.filter (fun i => π i ≠ i) with hS
      have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
      set m : Fin k := S.max' hSne with hmdef
      have hmS : m ∈ S := S.max'_mem hSne
      have hmne : π m ≠ m := by simpa [hS] using hmS
      have hgt : ∀ i, m < i → π i = i := by
        intro i hi
        by_contra hc
        have hiS : i ∈ S := by simp [hS, hc]
        exact absurd (S.le_max' i hiS) (not_le.mpr hi)
      have hπm : π m < m := by
        rcases lt_trichotomy (π m) m with h | h | h
        · exact h
        · exact absurd h hmne
        · exact absurd (π.injective (hgt (π m) h)) hmne
      set j : Fin k := π.symm m with hjdef
      have hjπ : π j = m := by rw [hjdef]; exact π.apply_symm_apply m
      have hj : j < m := by
        rcases lt_trichotomy j m with h | h | h
        · exact h
        · exact absurd (h ▸ hjπ) hmne
        · have h2 : π j = j := hgt j h
          rw [hjπ] at h2
          exact absurd h2 (ne_of_lt h)
      have hjm : j ≠ m := ne_of_lt hj
      set π' : Equiv.Perm (Fin k) := π * Equiv.swap j m with hπ'def
      have hπ'apply : ∀ i, π' i = π (Equiv.swap j m i) := by
        intro i; rw [hπ'def]; exact Equiv.Perm.mul_apply _ _ i
      have hπ'm : π' m = m := by rw [hπ'apply, Equiv.swap_apply_right, hjπ]
      have hπ'j : π' j = π m := by rw [hπ'apply, Equiv.swap_apply_left]
      have hπ'other : ∀ i, i ≠ j → i ≠ m → π' i = π i := by
        intro i h1 h2
        rw [hπ'apply, Equiv.swap_apply_of_ne_of_ne h1 h2]
      have hsupp : (Finset.univ.filter (fun i => π' i ≠ i)) ⊆ S.erase m := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        have him : i ≠ m := fun hc => hi (by rw [hc]; exact hπ'm)
        refine Finset.mem_erase.mpr ⟨him, ?_⟩
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h1 : i = j
        · rw [h1, hjπ]; exact hjm.symm
        · rw [hπ'other i h1 him] at hi; exact hi
      have hcard : (Finset.univ.filter (fun i => π' i ≠ i)).card ≤ n := by
        have h1 := Finset.card_le_card hsupp
        have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
        have h3 : 1 ≤ S.card := Finset.card_pos.mpr hSne
        omega
      have hsplit : ∀ F : Fin k → ℝ,
          ∑ i, F i = F j + F m + ∑ i ∈ (Finset.univ.erase j).erase m, F i := by
        intro F
        have h1 : m ∈ Finset.univ.erase j :=
          Finset.mem_erase.mpr ⟨hjm.symm, Finset.mem_univ m⟩
        rw [add_assoc, Finset.add_sum_erase _ F h1,
          Finset.add_sum_erase _ F (Finset.mem_univ j)]
      have hrest : ∀ i ∈ (Finset.univ.erase j).erase m,
          |a i - b (π' i)| = |a i - b (π i)| := by
        intro i hi
        have h2 : i ≠ m := (Finset.mem_erase.mp hi).1
        have h1 : i ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        rw [hπ'other i h1 h2]
      have hpair : |a j - b (π' j)| + |a m - b (π' m)|
          ≤ |a j - b (π j)| + |a m - b (π m)| := by
        rw [hπ'j, hπ'm, hjπ]
        exact four_point (ha hj.le) (hb hπm.le)
      have hle : ∑ i, |a i - b (π' i)| ≤ ∑ i, |a i - b (π i)| := by
        rw [hsplit (fun i => |a i - b (π' i)|), hsplit (fun i => |a i - b (π i)|),
          Finset.sum_congr rfl hrest]
        linarith [hpair]
      exact le_trans (ih π' hcard) hle

/-- On the real line, matching two configurations in sorted order is at least as cheap as
matching them in the given order: sorting is a contraction for the `ℓ¹` distance. -/
theorem solution (k : ℕ) (x y : Fin k → ℝ) :
    ∑ i, |(x ∘ Tuple.sort x) i - (y ∘ Tuple.sort y) i| ≤ ∑ i, |x i - y i| := by
  classical
  have ha : Monotone (x ∘ Tuple.sort x) := Tuple.monotone_sort x
  have hb : Monotone (y ∘ Tuple.sort y) := Tuple.monotone_sort y
  have hstep := sorted_le_perm_aux (x ∘ Tuple.sort x) (y ∘ Tuple.sort y) ha hb
    (Finset.univ.filter
      (fun i => ((Tuple.sort x).trans (Tuple.sort y).symm) i ≠ i)).card
    ((Tuple.sort x).trans (Tuple.sort y).symm) le_rfl
  refine le_trans hstep (le_of_eq ?_)
  have hterm : ∀ i : Fin k, |(x ∘ Tuple.sort x) i
      - (y ∘ Tuple.sort y) (((Tuple.sort x).trans (Tuple.sort y).symm) i)|
      = |x (Tuple.sort x i) - y (Tuple.sort x i)| := by
    intro i
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hterm i)]
  exact Fintype.sum_equiv (Tuple.sort x) _ _ (fun i => rfl)
