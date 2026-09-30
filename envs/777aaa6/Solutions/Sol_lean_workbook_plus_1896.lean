-- Prove2me | solution 1 for lean_workbook_plus_1896
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:19:24.724925+00:00
-- url     : https://prove2.me/submissions/0e0bfef7-78c5-4fb8-b8d2-c8ec3752c0f6

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

private theorem twice_choose_two (n : ℕ) : 2 * n.choose 2 + n = n * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith

private theorem choose_two_add (m n : ℕ) :
    (m + n).choose 2 = m.choose 2 + n.choose 2 + m * n := by
  nlinarith [twice_choose_two m, twice_choose_two n, twice_choose_two (m + n)]

def quadraticCocycle (r n : ℕ) : ℕ := n * r + n.choose 2

theorem quadratic_cocycle_add (r m n : ℕ) :
    quadraticCocycle r (m + n) = quadraticCocycle r m + quadraticCocycle r n + m * n := by
  simp only [quadraticCocycle, choose_two_add]
  ring

theorem positive_cocycle_classification (f : ℕ → ℕ) (r : ℕ) :
    (f 1 = r ∧ ∀ m n, 0 < m → 0 < n → f (m + n) = f m + f n + m * n) ↔
      ∀ n, 0 < n → f n = quadraticCocycle r n := by
  constructor
  · rintro ⟨h1, h⟩ n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst n
        simpa [quadraticCocycle] using h1
      · have hp : 0 < n := by omega
        rw [h n 1 hp (by omega), ih hp, h1]
        simp only [quadraticCocycle, Nat.choose_succ_succ, Nat.choose_one_right]
        ring
  · intro h
    constructor
    · simpa [quadraticCocycle] using h 1 (by omega)
    · intro m n hm hn
      rw [h (m + n) (by omega), h m hm, h n hn]
      exact quadratic_cocycle_add r m n

theorem natural_cocycle_classification (f : ℕ → ℕ) (r : ℕ) :
    (f 1 = r ∧ ∀ m n, f (m + n) = f m + f n + m * n) ↔
      ∀ n, f n = quadraticCocycle r n := by
  constructor
  · rintro ⟨h1, h⟩ n
    by_cases hn : n = 0
    · subst n
      have h0 := h 0 0
      norm_num at h0
      simp only [quadraticCocycle, Nat.choose_zero_succ, Nat.zero_mul, Nat.zero_add]
      omega
    · exact (positive_cocycle_classification f r).mp
        ⟨h1, fun m n _ _ => h m n⟩ n (by omega)
  · intro h
    constructor
    · simpa [quadraticCocycle] using h 1
    · intro m n
      rw [h (m + n), h m, h n]
      exact quadratic_cocycle_add r m n

theorem natural_cocycle_exists_unique (r : ℕ) :
    ∃! f : ℕ → ℕ, f 1 = r ∧ ∀ m n, f (m + n) = f m + f n + m * n := by
  refine ⟨quadraticCocycle r, (natural_cocycle_classification _ r).mpr (fun _ => rfl), ?_⟩
  intro f hf
  funext n
  exact (natural_cocycle_classification f r).mp hf n

def naturalCocycleEquiv : ℕ ≃ {f : ℕ → ℕ //
    ∀ m n, f (m + n) = f m + f n + m * n} where
  toFun r := ⟨quadraticCocycle r, quadratic_cocycle_add r⟩
  invFun f := f.1 1
  left_inv r := by simp [quadraticCocycle]
  right_inv f := by
    apply Subtype.ext
    funext n
    exact ((natural_cocycle_classification f.1 (f.1 1)).mp ⟨rfl, f.2⟩ n).symm

theorem quadratic_cocycle_one (n : ℕ) : quadraticCocycle 1 n = n * (n + 1) / 2 := by
  have h := twice_choose_two n
  have hh : 2 * quadraticCocycle 1 n = n * (n + 1) := by
    dsimp [quadraticCocycle]
    nlinarith
  omega

theorem solution (f : ℕ → ℕ) (hf : f 1 = 1)
    (hf1 : ∀ m n : ℕ, f (m + n) = f m + f n + m * n) :
    ∀ n : ℕ, f n = n * (n + 1) / 2 := by
  intro n
  rw [(natural_cocycle_classification f 1).mp ⟨hf, hf1⟩ n]
  exact quadratic_cocycle_one n
