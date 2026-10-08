-- Prove2me | solution 1 for Goldbach.aligned_cap_mass_finite
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T02:14:29.413283+00:00
-- url     : https://prove2.me/submissions/cd39c5cf-feaf-4371-b3cc-e85c744afaab

import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators
set_option autoImplicit false

namespace GoldbachAlignedCapMass
noncomputable section

private def prefixSum {n : ℕ} (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i, if i.val < k then f i else 0

private lemma prefix_zero {n : ℕ} (f : Fin n → ℝ) : prefixSum f 0 = 0 := by
  simp [prefixSum]

private lemma prefix_all {n : ℕ} (f : Fin n → ℝ) : prefixSum f n = ∑ i, f i := by
  simp [prefixSum]

private lemma prefix_truncate {n : ℕ} (f : Fin (n+1) → ℝ) (k : ℕ) (hk : k ≤ n) :
    prefixSum (fun i : Fin n => f i.castSucc) k = prefixSum f k := by
  have hs := Fin.sum_univ_castSucc (fun i : Fin (n+1) => if i.val < k then f i else 0)
  simpa only [Fin.val_castSucc, Fin.val_last, if_neg (not_lt_of_ge hk), add_zero,
    prefixSum] using hs.symm

private theorem weighted_prefix_le {n : ℕ} (r g w : Fin n → ℝ)
    (hprefix : ∀ k ≤ n, prefixSum r k ≤ prefixSum g k)
    (hw : Antitone w) (hw0 : ∀ i, 0 ≤ w i) :
    (∑ i, r i * w i) ≤ ∑ i, g i * w i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let last := Fin.last n
    let w' : Fin n → ℝ := fun i => w i.castSucc - w last
    have hprefix' : ∀ k ≤ n,
        prefixSum (fun i : Fin n => r i.castSucc) k ≤
        prefixSum (fun i : Fin n => g i.castSucc) k := by
      intro k hk
      rw [prefix_truncate r k hk, prefix_truncate g k hk]
      exact hprefix k (by omega)
    have hw' : Antitone w' := by
      intro i j hij
      exact sub_le_sub_right (hw (by exact hij)) _
    have hw0' : ∀ i, 0 ≤ w' i := by
      intro i
      apply sub_nonneg.mpr
      apply hw
      exact Fin.le_last _
    have hi := ih (fun i : Fin n => r i.castSucc) (fun i : Fin n => g i.castSucc)
      w' hprefix' hw' hw0'
    have hm := hprefix (n+1) (le_refl _)
    rw [prefix_all, prefix_all, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hm
    have hm' := mul_le_mul_of_nonneg_right hm (hw0 last)
    dsimp [w'] at hi
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hi
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    dsimp [last] at *
    nlinarith [hm']

private def greedy {n : ℕ} (a : Fin n → ℝ) (U : ℝ) (i : Fin n) : ℝ :=
  min (a i) (max 0 (U - prefixSum a i.val))

private lemma prefix_succ {n : ℕ} (f : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    prefixSum f (k+1) = prefixSum f k + f ⟨k,hk⟩ := by
  calc
    _ = prefixSum f k + ∑ i : Fin n, if i = ⟨k,hk⟩ then f i else 0 := by
      unfold prefixSum
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.val < k
      · have hneq : i ≠ ⟨k,hk⟩ := by
          intro h
          have hv := congrArg Fin.val h
          change i.val = k at hv
          omega
        simp [hi, show i.val < k+1 by omega, hneq]
      · by_cases he : i.val = k
        · have hie : i = ⟨k,hk⟩ := Fin.ext he
          subst i
          simp
        · simp [hi, show ¬ i.val < k+1 by omega,
            show i ≠ ⟨k,hk⟩ by intro h; apply he; exact congrArg Fin.val h]
    _ = _ := by simp

private lemma prefix_nonneg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (k : ℕ) :
    0 ≤ prefixSum f k := by
  apply Finset.sum_nonneg
  intro i _
  dsimp
  split_ifs
  · exact hf i
  · exact le_refl _

private lemma prefix_mono {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i)
    {k l : ℕ} (hkl : k ≤ l) : prefixSum f k ≤ prefixSum f l := by
  apply Finset.sum_le_sum
  intro i _
  dsimp
  split_ifs with hk hl hl
  · exact le_refl _
  · omega
  · exact hf i
  · exact le_refl _

private lemma prefix_greedy {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (U : ℝ) (hU : 0 ≤ U) (k : ℕ) (hk : k ≤ n) :
    prefixSum (greedy a U) k = min U (prefixSum a k) := by
  induction k with
  | zero => simp [prefix_zero, min_eq_right hU]
  | succ k ih =>
    have hkn : k < n := by omega
    rw [prefix_succ _ k hkn, prefix_succ _ k hkn, ih (by omega)]
    unfold greedy
    have hA := prefix_nonneg a ha k
    have hB := ha ⟨k,hkn⟩
    simp only [min_def, max_def]
    split_ifs <;> linarith

private lemma greedy_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i)
    (U : ℝ) (i : Fin n) : 0 ≤ greedy a U i := by
  exact le_min (ha i) (le_max_left _ _)

private lemma greedy_antitone {n : ℕ} (a : Fin n → ℝ)
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) (U : ℝ) : Antitone (greedy a U) := by
  intro i j hij
  apply min_le_min (ha hij)
  apply max_le_max_left
  exact sub_le_sub_left (prefix_mono a ha0 (by exact hij)) U

private lemma capped_prefix_le {n : ℕ} (r a : Fin n → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (ha0 : ∀ i, 0 ≤ a i) (hra : ∀ i, r i ≤ a i)
    (U : ℝ) (hU : 0 ≤ U) (hmass : (∑ i, r i) ≤ U) (k : ℕ) (hk : k ≤ n) :
    prefixSum r k ≤ prefixSum (greedy a U) k := by
  rw [prefix_greedy a ha0 U hU k hk]
  apply le_min
  · exact (prefix_mono r hr0 hk).trans (by simpa [prefix_all] using hmass)
  · apply Finset.sum_le_sum
    intro i _
    dsimp
    split_ifs
    · exact hra i
    · exact le_refl _

private lemma sorted_below_cap {n : ℕ} (r a : Fin n → ℝ) (ha : Antitone a)
    (hra : ∀ i, r i ≤ a i) (σ : Equiv.Perm (Fin n))
    (hs : Antitone (fun i => r (σ i))) (k : Fin n) : r (σ k) ≤ a k := by
  classical
  by_contra h
  have hk : a k < r (σ k) := lt_of_not_ge h
  have hcount : k.val < (Finset.univ.filter (fun i => a k < r (σ i))).card :=
    (Tuple.lt_card_gt_iff_apply_gt_of_antitone hs).mpr hk
  have hc : (Finset.univ.filter (fun i => a k < r (σ i))).card =
      (Finset.univ.filter (fun i => a k < r i)).card := by
    apply Finset.card_bij (fun i _ => σ i)
    · intro i hi
      simpa using hi
    · intro i hi j hj heq
      exact σ.injective heq
    · intro j hj
      refine ⟨σ.symm j, ?_, by simp⟩
      simpa using hj
  have hsub : (Finset.univ.filter (fun i => a k < r i)) ⊆ Finset.Iio k := by
    intro i hi
    apply Finset.mem_Iio.mpr
    by_contra hki
    have hai := ha (le_of_not_gt hki)
    have hri := hra i
    have hhi := (Finset.mem_filter.mp hi).2
    linarith
  have hbound := Finset.card_le_card hsub
  rw [Fin.card_Iio] at hbound
  rw [hc] at hcount
  omega

private lemma sorted_bilinear {n : ℕ} (r t a b : Fin n → ℝ)
    (ha : Antitone a) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (ht : Antitone t) (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hrmass : (∑ i, r i) ≤ U) (htmass : (∑ i, t i) ≤ V) :
    (∑ i, r i * t i) ≤ ∑ i, greedy a U i * greedy b V i := by
  have hrpref := capped_prefix_le r a hr0 ha0 hra U hU hrmass
  have htpref := capped_prefix_le t b ht0 hb0 htb V hV htmass
  have h1 := weighted_prefix_le r (greedy a U) t hrpref ht ht0
  have h2 := weighted_prefix_le t (greedy b V) (greedy a U) htpref
    (greedy_antitone a ha ha0 U) (greedy_nonneg a ha0 U)
  calc
    _ ≤ ∑ i, greedy a U i * t i := h1
    _ = ∑ i, t i * greedy a U i := by apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ ∑ i, greedy b V i * greedy a U i := h2
    _ = _ := by apply Finset.sum_congr rfl; intro i _; ring

private theorem bilinear_bound {n : ℕ} (r t a b : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b) (ha0 : ∀ i, 0 ≤ a i) (hb0 : ∀ i, 0 ≤ b i)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hrmass : (∑ i, r i) ≤ U) (htmass : (∑ i, t i) ≤ V) :
    (∑ i, r i * t i) ≤ ∑ i, greedy a U i * greedy b V i := by
  classical
  let σ := Tuple.sort (fun i => -(r i))
  let τ := Tuple.sort (fun i => -(t i))
  let rs : Fin n → ℝ := fun i => r (σ i)
  let ts : Fin n → ℝ := fun i => t (τ i)
  have hrs : Antitone rs := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -(r i)) hij
    change -(rs i) ≤ -(rs j) at hh
    linarith
  have hts : Antitone ts := by
    intro i j hij
    have hh := Tuple.monotone_sort (fun i => -(t i)) hij
    change -(ts i) ≤ -(ts j) at hh
    linarith
  have hrcap : ∀ i, rs i ≤ a i := sorted_below_cap r a ha hra σ hrs
  have htcap : ∀ i, ts i ≤ b i := sorted_below_cap t b hb htb τ hts
  have hrs0 : ∀ i, 0 ≤ rs i := fun i => hr0 (σ i)
  have hts0 : ∀ i, 0 ≤ ts i := fun i => ht0 (τ i)
  have hrsmass : (∑ i, rs i) ≤ U := by
    change (∑ i, r (σ i)) ≤ U
    rw [Equiv.sum_comp σ]
    exact hrmass
  have htsmass : (∑ i, ts i) ≤ V := by
    change (∑ i, t (τ i)) ≤ V
    rw [Equiv.sum_comp τ]
    exact htmass
  have hsorted := sorted_bilinear rs ts a b ha ha0 hb0 hts hrs0 hts0 hrcap htcap
    U V hU hV hrsmass htsmass
  have hrea := (hrs.monovary hts).sum_mul_comp_perm_le_sum_mul (σ := σ.trans τ.symm)
  calc
    _ = ∑ i, r (σ i) * t (σ i) := (Equiv.sum_comp σ (fun i => r i * t i)).symm
    _ ≤ ∑ i, rs i * ts i := by simpa [rs,ts,Equiv.trans_apply] using hrea
    _ ≤ _ := hsorted

private lemma square_sum_expand {n : ℕ} (r t : Fin n → ℝ) :
    (∑ i, (r i + t i)^2) = (∑ i, r i * r i) +
      2 * (∑ i, r i * t i) + (∑ i, t i * t i) := by
  calc
    _ = ∑ i, (r i * r i + 2 * (r i * t i) + t i * t i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum]

private theorem aligned_bound {n : ℕ} (r t a b : Fin n → ℝ)
    (ha : Antitone a) (hb : Antitone b)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (U V : ℝ) (hrmass : (∑ i, r i) ≤ U) (htmass : (∑ i, t i) ≤ V) :
    (∑ i, (r i+t i)^2) ≤ ∑ i, (greedy a U i+greedy b V i)^2 := by
  have ha0 : ∀ i, 0 ≤ a i := fun i => (hr0 i).trans (hra i)
  have hb0 : ∀ i, 0 ≤ b i := fun i => (ht0 i).trans (htb i)
  have hU : 0 ≤ U := (Finset.sum_nonneg (fun i _ => hr0 i)).trans hrmass
  have hV : 0 ≤ V := (Finset.sum_nonneg (fun i _ => ht0 i)).trans htmass
  have hrr := bilinear_bound r r a a ha ha ha0 ha0 hr0 hr0 hra hra
    U U hU hU hrmass hrmass
  have htt := bilinear_bound t t b b hb hb hb0 hb0 ht0 ht0 htb htb
    V V hV hV htmass htmass
  have hrt := bilinear_bound r t a b ha hb ha0 hb0 hr0 ht0 hra htb
    U V hU hV hrmass htmass
  rw [square_sum_expand,square_sum_expand]
  linarith

end
end GoldbachAlignedCapMass

theorem solution (n : ℕ) (a b r t : Fin n → ℝ) (U V : ℝ)
    (ha : Antitone a) (hb : Antitone b)
    (hr0 : ∀ i, 0 ≤ r i) (ht0 : ∀ i, 0 ≤ t i)
    (hra : ∀ i, r i ≤ a i) (htb : ∀ i, t i ≤ b i)
    (hrmass : (∑ i, r i) ≤ U) (htmass : (∑ i, t i) ≤ V) :
    (∑ i, (r i+t i)^2) ≤ ∑ i,
      (min (a i) (max 0 (U - ∑ j : Fin n, if j.val < i.val then a j else 0)) +
       min (b i) (max 0 (V - ∑ j : Fin n, if j.val < i.val then b j else 0)))^2 := by
  exact GoldbachAlignedCapMass.aligned_bound r t a b ha hb hr0 ht0 hra htb U V hrmass htmass

#print axioms solution
