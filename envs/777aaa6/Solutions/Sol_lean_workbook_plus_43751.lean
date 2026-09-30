-- Prove2me | solution 1 for lean_workbook_plus_43751
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:59.144193+00:00
-- url     : https://prove2.me/submissions/c1e5c44f-8e16-4eb2-a862-16d2c8ccf202

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

namespace PositiveDifferenceDivisibility

theorem translated_pair (x y L : ℕ) (hxy : x ≤ y)
    (hpair : y - x ∣ y + x) (hxL : x ∣ L) :
    (L + y) - (L + x) ∣ (L + y) + (L + x) := by
  have hsub := Nat.dvd_sub hpair (dvd_refl (y - x))
  have htwo : y - x ∣ 2 * x := by
    convert hsub using 1
    omega
  have htwoL : y - x ∣ 2 * L := htwo.trans (mul_dvd_mul_left 2 hxL)
  have hsum := dvd_add hpair htwoL
  convert hsum using 1 <;> omega

theorem positive_increasing_sequence (n : ℕ) :
    ∃ a : ℕ → ℕ, (∀ i, 0 < a i) ∧ StrictMono a ∧
      ∀ i j, i < j → j ≤ n → (a j - a i) ∣ (a j + a i) := by
  induction n with
  | zero =>
      refine ⟨fun i => i + 1, ?_, ?_, ?_⟩
      · intro i
        exact Nat.zero_lt_succ i
      · intro i j hij
        exact Nat.add_lt_add_right hij 1
      · intro i j hij hj
        omega
  | succ n ih =>
      obtain ⟨a, hpos, hmono, hpair⟩ := ih
      let L : ℕ := ∏ i ∈ Finset.range (n + 1), a i
      have hLpos : 0 < L := Finset.prod_pos (fun i _ => hpos i)
      have hdivL : ∀ i, i ≤ n → a i ∣ L := by
        intro i hi
        exact Finset.dvd_prod_of_mem a (Finset.mem_range.mpr (by omega))
      let b : ℕ → ℕ := fun | 0 => L | i + 1 => L + a i
      have hbpos : ∀ i, 0 < b i := by
        intro i
        cases i with
        | zero => exact hLpos
        | succ i => exact Nat.add_pos_right L (hpos i)
      have hbmono : StrictMono b := by
        apply strictMono_nat_of_lt_succ
        intro i
        cases i with
        | zero =>
            change L < L + a 0
            have h := hpos 0
            omega
        | succ i =>
            exact Nat.add_lt_add_left (hmono (Nat.lt_succ_self i)) L
      refine ⟨b, hbpos, hbmono, ?_⟩
      intro i j hij hj
      cases j with
      | zero => omega
      | succ j =>
          have hjn : j ≤ n := by omega
          cases i with
          | zero =>
              have hsum := dvd_add (dvd_refl (a j))
                (dvd_add (hdivL j hjn) (hdivL j hjn))
              change (L + a j) - L ∣ (L + a j) + L
              convert hsum using 1 <;> omega
          | succ i =>
              have hij' : i < j := by omega
              exact translated_pair (a i) (a j) L (hmono.monotone (Nat.le_of_lt hij'))
                (hpair i j hij' hjn) (hdivL i (by omega))

end PositiveDifferenceDivisibility

theorem solution (n : ℕ) (_hn : 2 ≤ n) :
    ∃ a : ℕ → ℕ, ∀ i j : ℕ, i < j → i ≤ n ∧ j ≤ n →
      (a j - a i) ∣ (a j + a i) := by
  obtain ⟨a, _, _, hpair⟩ := PositiveDifferenceDivisibility.positive_increasing_sequence n
  exact ⟨a, fun i j hij hj => hpair i j hij hj.2⟩
