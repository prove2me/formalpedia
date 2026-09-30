-- Prove2me | solution 1 for lean_workbook_plus_53186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:34:19.996083+00:00
-- url     : https://prove2.me/submissions/2433d972-13dc-4099-ad59-dda12d6e8926

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PositiveDivisibilityChain

def Adjacent (a b : ℤ) : Prop := a + b ∣ a * b

theorem Adjacent.symm {a b : ℤ} (h : Adjacent a b) : Adjacent b a := by
  simpa [Adjacent, add_comm, mul_comm] using h

inductive Reach : ℤ → ℤ → Prop
  | refl {a : ℤ} (ha : 2 < a) : Reach a a
  | cons {a b c : ℤ} (ha : 2 < a) (hab : Adjacent a b) (hbc : Reach b c) : Reach a c

theorem Reach.left_pos {a b : ℤ} (h : Reach a b) : 2 < a := by
  cases h with
  | refl ha => exact ha
  | cons ha _ _ => exact ha

theorem Reach.edge {a b : ℤ} (ha : 2 < a) (hb : 2 < b) (hab : Adjacent a b) :
    Reach a b := .cons ha hab (.refl hb)

theorem Reach.trans {a b c : ℤ} (hab : Reach a b) (hbc : Reach b c) : Reach a c := by
  induction hab with
  | refl _ => exact hbc
  | cons ha hadj _ ih => exact .cons ha hadj (ih hbc)

theorem Reach.symm {a b : ℤ} (h : Reach a b) : Reach b a := by
  induction h with
  | refl ha => exact .refl ha
  | cons ha hab hbc ih => exact ih.trans (.edge hbc.left_pos ha hab.symm)

theorem Reach.realize {a b : ℤ} (h : Reach a b) :
    ∃ k : ℕ, ∃ f : ℕ → ℤ, f 0 = a ∧ f k = b ∧
      (∀ i, i ≤ k → 2 < f i) ∧ (∀ i, i < k → Adjacent (f i) (f (i + 1))) := by
  induction h with
  | @refl a ha =>
      exact ⟨0, fun _ => a, rfl, rfl, fun _ _ => ha, fun _ hi => by omega⟩
  | @cons a b c ha hab hbc ih =>
      obtain ⟨k, f, hf0, hfk, hpos, hedge⟩ := ih
      let g : ℕ → ℤ := fun | 0 => a | i + 1 => f i
      refine ⟨k + 1, g, rfl, hfk, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact ha
        | succ i => exact hpos i (by omega)
      · intro i hi
        cases i with
        | zero => simpa [g, hf0] using hab
        | succ i => exact hedge i (by omega)

theorem product_pos (a b : ℤ) (ha : 2 < a) (hb : 1 ≤ b) : 2 < a * b := by
  nlinarith [mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ b - 1 by omega)]

theorem basic (n : ℤ) (hn : 2 < n) : Reach n (n * (n - 1)) := by
  apply Reach.edge hn (product_pos n (n - 1) hn (by omega))
  exact ⟨n - 1, by ring⟩

theorem doubling (n : ℤ) (hn : 2 < n) : Reach n (2 * n) := by
  have h1 : 2 < n * (n - 1) := product_pos n (n - 1) hn (by omega)
  have h2 : 2 < n * (n - 1) * (n - 2) :=
    product_pos (n * (n - 1)) (n - 2) h1 (by omega)
  have h3 : 2 < n * (n - 2) := product_pos n (n - 2) hn (by omega)
  have e2 : Adjacent (n * (n - 1)) (n * (n - 1) * (n - 2)) :=
    ⟨n * (n - 2), by ring⟩
  have e3 : Adjacent (n * (n - 1) * (n - 2)) (n * (n - 2)) :=
    ⟨(n - 1) * (n - 2), by ring⟩
  have e4 : Adjacent (n * (n - 2)) (2 * n) := ⟨2 * (n - 2), by ring⟩
  exact (basic n hn).trans ((Reach.edge h1 h2 e2).trans
    ((Reach.edge h2 h3 e3).trans (Reach.edge h3 (by omega) e4)))

theorem predecessor (n : ℤ) (hn : 3 < n) : Reach n (n - 1) := by
  have hn2 : 2 < n := by omega
  have h1 : 2 < n * (n - 1) := product_pos n (n - 1) hn2 (by omega)
  have h2 : 2 < n * (n - 1) * (n - 2) :=
    product_pos (n * (n - 1)) (n - 2) h1 (by omega)
  have h3 : 2 < n * (n - 1) * (n - 2) * (n - 3) :=
    product_pos (n * (n - 1) * (n - 2)) (n - 3) h2 (by omega)
  have hm : 2 < (n - 1) * (n - 2) :=
    product_pos (n - 1) (n - 2) (by omega) (by omega)
  have e2 : Adjacent (n * (n - 1)) (n * (n - 1) * (n - 2)) :=
    ⟨n * (n - 2), by ring⟩
  have e3 : Adjacent (n * (n - 1) * (n - 2))
      (n * (n - 1) * (n - 2) * (n - 3)) := ⟨n * (n - 1) * (n - 3), by ring⟩
  have e4 : Adjacent (n * (n - 1) * (n - 2) * (n - 3))
      (2 * ((n - 1) * (n - 2))) := ⟨2 * n * (n - 3), by ring⟩
  have hfirst : Reach n (2 * ((n - 1) * (n - 2))) :=
    (basic n hn2).trans ((Reach.edge h1 h2 e2).trans
      ((Reach.edge h2 h3 e3).trans (Reach.edge h3 (by omega) e4)))
  have hlast : Reach ((n - 1) * (n - 2)) (n - 1) := by
    convert (basic (n - 1) (by omega)).symm using 1
    ring
  exact hfirst.trans ((doubling ((n - 1) * (n - 2)) hm).symm.trans hlast)

theorem nat_to_three (k : ℕ) : Reach ((k : ℤ) + 3) 3 := by
  induction k with
  | zero => exact .refl (by norm_num)
  | succ k ih =>
      have h := predecessor ((k : ℤ) + 4) (by omega)
      have h' : Reach ((k : ℤ) + 4) ((k : ℤ) + 3) := by convert h using 1; ring
      simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h'.trans ih

theorem to_three (a : ℤ) (ha : 2 < a) : Reach a 3 := by
  have hcast : ((a - 3).toNat : ℤ) = a - 3 := Int.toNat_of_nonneg (by omega)
  have h := nat_to_three (a - 3).toNat
  simpa [hcast] using h

theorem full_chain (a b : ℤ) (ha : 2 < a) (hb : 2 < b) :
    ∃ k : ℕ, ∃ n : ℕ → ℤ, n 0 = a ∧ n k = b ∧
      (∀ i, i ≤ k → 2 < n i) ∧
      (∀ i, i < k → (n i + n (i + 1)) ∣ n i * n (i + 1)) := by
  exact ((to_three a ha).trans (to_three b hb).symm).realize

end PositiveDivisibilityChain

theorem solution (a b : ℤ) (hab : 2 < a ∧ 2 < b) :
    ∃ k : ℕ, ∃ n : ℕ → ℤ, n 0 = a ∧ n k = b ∧
      ∀ i, 0 < i ∧ i < k → (n i + n (i + 1)) ∣ n i * n (i + 1) := by
  obtain ⟨k, n, h0, hk, _, hedge⟩ := PositiveDivisibilityChain.full_chain a b hab.1 hab.2
  exact ⟨k, n, h0, hk, fun i hi => hedge i hi.2⟩
