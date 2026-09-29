-- Prove2me | solution 1 for AlmostLossless.twoUniversal_dotHash
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T13:19:12.375889+00:00
-- url     : https://prove2.me/submissions/a80393aa-c2a5-4e3e-b137-678e8c907a5c

import Definitions.Def_Logic_AlmostLossless_Hashing
open AlmostLossless in
theorem solution {p k : ℕ} [Fact p.Prime] : TwoUniversal (dotHash p k) := by
  intro x y hxy
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := Function.ne_iff.mp hxy
  have hd : x j - y j ≠ 0 := sub_ne_zero.mpr hj
  let f : (Fin k → ZMod p) → ZMod p := fun a => ∑ i, a i * (x i - y i)
  have hf_add : ∀ a b, f (a + b) = f a + f b := by
    intro a b
    simp only [f, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hfsmul : ∀ (c : ZMod p) a, f (c • a) = c * f a := by
    intro c a
    simp only [f, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  let v : Fin k → ZMod p := Pi.single j (x j - y j)⁻¹
  have hfv : f v = 1 := by
    simp only [f, v, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    exact inv_mul_cancel₀ hd
  have hcoll : ∀ a, dotHash p k a x = dotHash p k a y ↔ f a = 0 := by
    intro a
    simp only [dotHash, f, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  have hfiber : ∀ c : ZMod p, (Finset.univ.filter (fun a => f a = c)).card
      = (Finset.univ.filter (fun a => f a = 0)).card := by
    intro c
    apply Finset.card_bij (fun a _ => a - c • v)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [sub_eq_add_neg, hf_add, ← neg_smul, hfsmul, hfv, ha]
      ring
    · intro a _ b _ h
      exact sub_left_injective h
    · intro b hb
      refine ⟨b + c • v, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      rw [hf_add, hfsmul, hfv, hb]
      ring
  have htotal : Fintype.card (Fin k → ZMod p)
      = ∑ c : ZMod p, (Finset.univ.filter (fun a => f a = c)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (f a))
  have hset : (Finset.univ.filter (fun a => dotHash p k a x = dotHash p k a y))
      = Finset.univ.filter (fun a => f a = 0) := Finset.filter_congr (fun a _ => hcoll a)
  rw [hset, htotal]
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm]
