-- Prove2me | solution 1 for EMLLyapunovNL.nlMle_dilationCell
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:07:50.80539+00:00
-- url     : https://prove2.me/submissions/cd578371-3230-43e9-9265-244575048afd

import Mathlib
import Definitions.Def_Novelty_EMLLyapunovTropical
open Filter EMLLyapunovNL in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {r : ℝ}
    (hr : r ≠ 0) : nlMle (dilationCell (E := E) r) = Real.log |r| := by
  -- iterates of the dilation are dilations
  have hiter : ∀ T : ℕ, (dilationCell (E := E) r)^[T] = fun x => r ^ T • x := by
    intro T
    induction T with
    | zero => funext x; simp
    | succ T ih =>
      funext x
      rw [Function.iterate_succ_apply', ih]
      simp only [dilationCell, smul_smul, pow_succ, mul_comm]
  -- the optimal Lipschitz constant of `x ↦ c • x` is `|c|`
  have hlip : ∀ c : ℝ, optLip (fun x : E => c • x) = |c| := by
    intro c
    have hset : lipSet (fun x : E => c • x) = Set.Ici |c| := by
      ext K
      simp only [lipSet, Set.mem_setOf_eq, Set.mem_Ici, dist_smul₀, Real.norm_eq_abs]
      constructor
      · rintro ⟨-, hK⟩
        obtain ⟨v, hv⟩ := exists_ne (0 : E)
        have hd : 0 < dist v 0 := dist_pos.mpr hv
        exact le_of_mul_le_mul_right (hK v 0) hd
      · intro hK
        exact ⟨(abs_nonneg c).trans hK, fun x y => mul_le_mul_of_nonneg_right hK dist_nonneg⟩
    unfold optLip
    rw [hset, csInf_Ici]
  -- so every finite-time exponent (for `T ≥ 1`) equals `log |r|`
  have hftle : ∀ T : ℕ, 1 ≤ T → nlFtle (dilationCell (E := E) r) T = Real.log |r| := by
    intro T hT
    unfold nlFtle
    rw [hiter, hlip, abs_pow, Real.log_pow]
    have : (T : ℝ) ≠ 0 := by exact_mod_cast (show T ≠ 0 by omega)
    field_simp
  unfold nlMle
  rw [limsup_congr (Filter.eventually_atTop.mpr ⟨1, fun T hT => hftle T hT⟩), limsup_const]
