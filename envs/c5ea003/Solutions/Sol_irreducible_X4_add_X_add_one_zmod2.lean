-- Prove2me | solution 1 for irreducible_X4_add_X_add_one_zmod2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T09:21:40.889109+00:00
-- url     : https://prove2.me/submissions/bb5b6e9d-2b75-4d0f-885d-9adaed632e42

import Mathlib
import Definitions.Def_Bridges_IrreducibleTransfer
open Polynomial Finset in
theorem solution :
    Irreducible (poly_X4_X_1 (ZMod 2)) := by
  have hmon : (poly_X4_X_1 (ZMod 2)).Monic := by unfold poly_X4_X_1; monicity!
  have hdeg : (poly_X4_X_1 (ZMod 2)).natDegree = 4 := by unfold poly_X4_X_1; compute_degree!
  -- no roots in `𝔽₂`
  have heval : ∀ r : ZMod 2, eval r (poly_X4_X_1 (ZMod 2)) ≠ 0 := by
    intro r
    unfold poly_X4_X_1
    simp only [eval_add, eval_pow, eval_X, eval_one]
    revert r
    decide
  rw [hmon.irreducible_iff_natDegree']
  refine ⟨fun h => by have := congrArg natDegree h; rw [hdeg, natDegree_one] at this; omega, ?_⟩
  intro f g _ hg hfg hmem
  rw [hdeg, Finset.mem_Ioc] at hmem
  -- a root of a factor would be a root of the polynomial
  have hroot : ∀ r : ZMod 2, eval r g ≠ 0 := fun r h => heval r (by rw [← hfg, eval_mul, h, mul_zero])
  have hlc : g.coeff g.natDegree = 1 := hg.coeff_natDegree
  have hev : ∀ r : ZMod 2, eval r g = ∑ i ∈ range (g.natDegree + 1), g.coeff i * r ^ i :=
    fun r => eval_eq_sum_range r
  have h12 : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
  rcases h12 with h1 | h2
  · -- a monic linear factor `X + c` has the root `-c`
    apply hroot (-g.coeff 0)
    rw [hev, h1, sum_range_succ, sum_range_one]
    rw [h1] at hlc
    rw [hlc]
    ring
  · -- a monic quadratic factor without roots must be `X² + X + 1`
    rw [h2] at hlc
    have hc : g.coeff 0 = 1 ∧ g.coeff 1 = 1 := by
      have key : ∀ c0 c1 : ZMod 2, (∀ r : ZMod 2, c0 * r ^ 0 + c1 * r ^ 1 + 1 * r ^ 2 ≠ 0) →
          c0 = 1 ∧ c1 = 1 := by decide
      refine key _ _ fun r => ?_
      have := hroot r
      rwa [hev, h2, sum_range_succ, sum_range_succ, sum_range_one, hlc] at this
    have hgX : g = X ^ 2 + X + 1 := by
      rw [hg.as_sum, h2, sum_range_succ, sum_range_one, hc.1, hc.2]
      simp
      ring
    -- `X⁴ + X + 1 = (X² + X + 1)(X² + X) + 1`, so the factor would divide `1`
    have h2z : (2 : (ZMod 2)[X]) = 0 := CharTwo.two_eq_zero
    have hsplit : poly_X4_X_1 (ZMod 2) = g * (X ^ 2 + X) + 1 := by
      rw [hgX]
      unfold poly_X4_X_1
      linear_combination (-(X ^ 3 + X ^ 2) : (ZMod 2)[X]) * h2z
    have hdvd : g ∣ 1 := by
      have : g ∣ g * (X ^ 2 + X) + 1 := hsplit ▸ Dvd.intro_left f hfg
      exact (dvd_add_right (dvd_mul_right g _)).mp this
    have := natDegree_eq_zero_of_isUnit (isUnit_of_dvd_one hdvd)
    omega
