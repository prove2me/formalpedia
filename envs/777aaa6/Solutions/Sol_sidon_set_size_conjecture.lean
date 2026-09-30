-- Prove2me | solution 1 for sidon_set_size_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:09.906538+00:00
-- url     : https://prove2.me/submissions/dff292aa-6868-486a-8a76-ecba7264b33e

import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private theorem sidon_card_sq_le {n : ℕ} (S : Finset (Fin n))
    (hS : ∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
      a ≠ b → a.val + b.val = c.val + d.val →
        ({a, b} : Finset (Fin n)) = {c, d}) : S.card * S.card ≤ 5 * n := by
  classical
  let encode : S.offDiag → Fin (2 * n) × Bool := fun p =>
    (⟨p.1.1.val + p.1.2.val, by
      have ha := p.1.1.isLt
      have hb := p.1.2.isLt
      omega⟩, decide (p.1.1 < p.1.2))
  have hinj : Function.Injective encode := by
    intro p q heq
    rcases p with ⟨⟨a, b⟩, hp⟩
    rcases q with ⟨⟨c, d⟩, hq⟩
    have hsum : a.val + b.val = c.val + d.val :=
      congrArg (fun x : Fin (2 * n) × Bool => x.1.val) heq
    have hbits : decide (a < b) = decide (c < d) := congrArg Prod.snd heq
    have hp' := Finset.mem_offDiag.mp hp
    have hq' := Finset.mem_offDiag.mp hq
    have hpair := hS a b c d hp'.1 hp'.2.1 hq'.1 hq'.2.1 hp'.2.2 hsum
    have ha : a = c ∨ a = d := by
      have : a ∈ ({c, d} : Finset (Fin n)) := by
        rw [← hpair]
        simp
      simpa using this
    rcases ha with hac | had
    · subst c
      have hbd : b = d := Fin.ext (by omega)
      subst d
      rfl
    · subst d
      have hbc : b = c := Fin.ext (by omega)
      subst c
      have hiff : (a < b) ↔ (b < a) := decide_eq_decide.mp hbits
      exfalso
      rcases lt_or_gt_of_ne hp'.2.2 with hlt | hgt
      · exact lt_asymm hlt (hiff.mp hlt)
      · exact lt_asymm hgt (hiff.mpr hgt)
  have hcount := Fintype.card_le_of_injective encode hinj
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Finset.offDiag_card] at hcount
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  omega

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (S : Finset (Fin n)),
      (∀ a b c d : Fin n, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
        a ≠ b → (a.val + b.val = c.val + d.val) →
          ({a, b} : Finset (Fin n)) = {c, d}) →
      (S.card : ℝ) ≤ C * Real.sqrt n * (1 + eps) := by
  intro eps heps
  refine ⟨3, by norm_num, ?_⟩
  intro n S hS
  have hbound : (S.card : ℝ) * S.card ≤ 5 * n := by
    exact_mod_cast sidon_card_sq_le S hS
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcard : (0 : ℝ) ≤ S.card := Nat.cast_nonneg S.card
  have hroot := Real.sqrt_nonneg (n : ℝ)
  have hroot_sq := Real.sq_sqrt hn
  have hthree : 0 ≤ 3 * Real.sqrt (n : ℝ) := by linarith
  have hsq : (S.card : ℝ) ^ 2 ≤ (3 * Real.sqrt (n : ℝ)) ^ 2 := by
    nlinarith
  have hle : (S.card : ℝ) ≤ 3 * Real.sqrt (n : ℝ) :=
    (sq_le_sq₀ hcard hthree).mp hsq
  nlinarith [mul_nonneg hthree (le_of_lt heps)]

#print axioms solution
