-- Prove2me | solution 1 for Logic.QRDial.sum_pattern_prod
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:17:53.642706+00:00
-- url     : https://prove2.me/submissions/d101d5e0-8efd-4441-968c-376e34539b58

import Mathlib
import Definitions.Def_Logic_QRDialDispersionLaws
import Definitions.Def_Logic_QRDialOrthogonality
open Logic.QRDial in
theorem solution {σ : Type*} [Fintype σ] (a b : σ → ℝ)
    (ha : ∑ s, a s = 0) (hb : ∑ s, b s = 0) (hab : ∑ s, a s * b s = 0) :
    ∀ k : ℕ, ∑ w : Fin k → σ, (∑ i, a (w i)) * (∑ i, b (w i)) = 0 := by
  have hsingle : ∀ (c : σ → ℝ), (∑ s, c s = 0) → ∀ k : ℕ, ∑ w : Fin k → σ, (∑ i, c (w i)) = 0 := by
    intro c hc
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (fun w => ∑ i, c (w i)),
        Fintype.sum_prod_type]
      have hterm : ∀ (s : σ) (v : Fin k → σ),
          (∑ i : Fin (k + 1), c ((Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (s, v) i))
            = c s + ∑ i : Fin k, c (v i) := by
        intro s v
        rw [Fin.sum_univ_succ]
        simp [Fin.consEquiv]
      simp only [hterm]
      have hrow : ∀ s : σ, (∑ _v : Fin k → σ, (c s + ∑ i : Fin k, c (_v i)))
          = (Fintype.card (Fin k → σ)) • c s := by
        intro s
        rw [Finset.sum_add_distrib, ih, add_zero, Finset.sum_const, Finset.card_univ]
      simp only [hrow]
      rw [← Finset.smul_sum, hc, smul_zero]
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (k + 1) => σ))
        (fun w => (∑ i, a (w i)) * (∑ i, b (w i))), Fintype.sum_prod_type]
    have hterm : ∀ (s : σ) (v : Fin k → σ),
        (∑ i : Fin (k + 1), a ((Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (s, v) i))
          * (∑ i : Fin (k + 1), b ((Fin.consEquiv (fun _ : Fin (k + 1) => σ)) (s, v) i))
          = a s * b s + a s * (∑ i : Fin k, b (v i)) + (∑ i : Fin k, a (v i)) * b s
            + (∑ i : Fin k, a (v i)) * (∑ i : Fin k, b (v i)) := by
      intro s v
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
      ring
    simp only [hterm]
    have erow : ∀ s : σ,
        (∑ _v : Fin k → σ, (a s * b s + a s * (∑ i : Fin k, b (_v i))
          + (∑ i : Fin k, a (_v i)) * b s + (∑ i : Fin k, a (_v i)) * (∑ i : Fin k, b (_v i))))
        = (Fintype.card (Fin k → σ)) • (a s * b s) := by
      intro s
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, ← Finset.mul_sum, hsingle b hb k, mul_zero,
        ← Finset.sum_mul, hsingle a ha k, zero_mul, ih]
      simp
    simp only [erow]
    rw [← Finset.smul_sum, hab, smul_zero]
