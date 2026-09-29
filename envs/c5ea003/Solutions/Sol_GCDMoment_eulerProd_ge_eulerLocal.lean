-- Prove2me | solution 1 for GCDMoment.eulerProd_ge_eulerLocal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T11:05:49.295698+00:00
-- url     : https://prove2.me/submissions/c1830d65-e6a1-4780-a135-5bec758a9393

import Mathlib
import Definitions.Def_Novelty_GCDMomentMultiplicative
open GCDMoment in
theorem solution {k : ℕ} (hk : 1 ≤ k) : ∀ (l : List ℤ), l ≠ [] →
    (∀ a ∈ l, 2 ≤ a) → eulerLocal k l.prod ≤ eulerProd k l := by
  -- a nonempty list of integers `≥ 2` has product `≥ 2`
  have hprod2 : ∀ l : List ℤ, l ≠ [] → (∀ a ∈ l, 2 ≤ a) → 2 ≤ l.prod := by
    intro l
    induction l with
    | nil => intro h; exact absurd rfl h
    | cons b rest ih =>
      intro _ hall
      have hb : 2 ≤ b := hall b (List.mem_cons_self ..)
      by_cases hr : rest = []
      · subst hr; simpa using hb
      · have hrest := ih hr (fun c hc => hall c (List.mem_cons_of_mem b hc))
        have : (b :: rest).prod = b * rest.prod := by simp
        rw [this]
        nlinarith
  intro l
  induction l with
  | nil => intro h; exact absurd rfl h
  | cons a rest ih =>
    intro _ hall
    have ha : 2 ≤ a := hall a (List.mem_cons_self ..)
    by_cases hr : rest = []
    · subst hr
      simp [eulerProd, eulerLocal]
    · have hrest : ∀ b ∈ rest, 2 ≤ b := fun b hb => hall b (List.mem_cons_of_mem a hb)
      have hP2 : 2 ≤ rest.prod := hprod2 rest hr hrest
      have hih := ih hr hrest
      have hak : a ≤ a ^ k := by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ k := pow_le_pow_right₀ (by linarith) hk
      have hPk : rest.prod ≤ rest.prod ^ k := by
        calc rest.prod = rest.prod ^ 1 := (pow_one _).symm
          _ ≤ rest.prod ^ k := pow_le_pow_right₀ (by linarith) hk
      show eulerLocal k (a * rest.prod) ≤ eulerLocal k a * eulerProd k rest
      simp only [eulerLocal] at hih ⊢
      rw [mul_pow]
      nlinarith [hih, ha, hP2, hak, hPk,
        mul_nonneg (by linarith : (0:ℤ) ≤ rest.prod - 1) (by linarith : (0:ℤ) ≤ a ^ k - 1),
        mul_nonneg (by linarith : (0:ℤ) ≤ rest.prod ^ k - 1) (by linarith : (0:ℤ) ≤ a - 1)]
