-- Prove2me | solution 1 for MarkoffTransfer.markoff_reach_ordered
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T12:49:36.724045+00:00
-- url     : https://prove2.me/submissions/9814cf02-e175-4ffa-a596-92dfc10edd55

import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
open MarkoffTransfer in
theorem solution :
    ∀ N : ℕ, ∀ x y z : ℤ, x + y + z ≤ (N : ℤ) → 0 < x → x ≤ y → y ≤ z → IsMarkoff x y z →
      MReach x y z := by
  -- reachability is closed under all permutations
  have hperm : ∀ {a b c : ℤ}, MReach a b c →
      MReach c b a ∧ MReach b c a ∧ MReach c a b := fun h =>
    ⟨h.swap₂₃.swap₁₂.swap₂₃, h.swap₁₂.swap₂₃, h.swap₂₃.swap₁₂⟩
  -- descent on sorted triples, by induction on the sum
  have key : ∀ n : ℕ, ∀ a b c : ℤ, 0 < a → 0 < b → 0 < c → a ≤ b → b ≤ c →
      IsMarkoff a b c → (a + b + c).toNat ≤ n → MReach a b c := by
    intro n
    induction n with
    | zero => intro a b c ha hb hc _ _ _ hn; omega
    | succ n ih =>
      intro a b c ha hb hc hab hbc hM hn
      have hM0 : a ^ 2 + b ^ 2 + c ^ 2 - 3 * a * b * c = 0 := hM
      by_cases hcb : c = b
      · -- the only Markoff triple with two equal top entries is `(1,1,1)`
        subst hcb
        have ha1 : a ≤ 1 := by
          by_contra h
          push_neg at h
          nlinarith [mul_pos (pow_pos hc 2) (sub_pos.mpr h), mul_le_mul hab hab ha.le hc.le]
        have ha1' : a = 1 := by omega
        subst ha1'
        have hc1 : c = 1 := by nlinarith
        subst hc1
        exact MReach.root
      · have hbc' : b < c := lt_of_le_of_ne hbc (Ne.symm hcb)
        -- the Vieta partner `c' = 3ab − c` satisfies `c · c' = a² + b²` and `0 < c' ≤ b`
        obtain ⟨c', hc'⟩ : ∃ c', c' = 3 * a * b - c := ⟨_, rfl⟩
        have hprod : c * c' = a ^ 2 + b ^ 2 := by rw [hc']; nlinarith
        have hc'pos : 0 < c' := by
          by_contra h
          push_neg at h
          nlinarith [mul_nonpos_of_nonneg_of_nonpos hc.le h]
        have hc'le : c' ≤ b := by
          by_contra h
          push_neg at h
          have hf : (b - c) * (b - c') = a ^ 2 + b ^ 2 * (2 - 3 * a) := by
            rw [hc']; nlinarith
          nlinarith [mul_pos (sub_pos.mpr hbc') (sub_pos.mpr h), mul_le_mul hab hab ha.le hb.le,
            mul_nonneg (sq_nonneg b) (sub_nonneg.mpr (show (1 : ℤ) ≤ a by omega))]
        have hM' : IsMarkoff a b c' := by
          show a ^ 2 + b ^ 2 + c' ^ 2 - 3 * a * b * c' = 0
          rw [hc']
          nlinarith
        have hR : MReach a b c' := by
          rcases le_total c' a with h | h
          · have h1 := ih c' a b hc'pos ha hb h hab
              (by show c' ^ 2 + a ^ 2 + b ^ 2 - 3 * c' * a * b = 0
                  have : a ^ 2 + b ^ 2 + c' ^ 2 - 3 * a * b * c' = 0 := hM'
                  linarith)
              (by omega)
            exact (hperm h1).2.1
          · have h1 := ih a c' b ha hc'pos hb h hc'le
              (by show a ^ 2 + c' ^ 2 + b ^ 2 - 3 * a * c' * b = 0
                  have : a ^ 2 + b ^ 2 + c' ^ 2 - 3 * a * b * c' = 0 := hM'
                  linarith)
              (by omega)
            exact h1.swap₂₃
        have hv : vieta a b c' = c := by unfold vieta; rw [hc']; ring
        rw [← hv]
        exact hR.vieta
  intro N x y z hN hx hxy hyz hM
  exact key N x y z hx (by omega) (by omega) hxy hyz hM (by omega)
