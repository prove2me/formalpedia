-- Prove2me | solution 1 for conj_riemannZeta_conj_aux1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:37:22.928742+00:00
-- url     : https://prove2.me/submissions/5df01ade-1e10-41d3-97d2-fbf84354d8e6

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate

theorem solution (s : ℂ) (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa)]
  rw [Complex.conj_tsum]
  congr
  ext n
  have h1 : n + 1 ≠ 0 := by linarith
  have h2 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast h1
  rw [Complex.cpow_def_of_ne_zero h2, Complex.cpow_def_of_ne_zero h2, RCLike.conj_div, map_one,
    ← Complex.exp_conj, map_mul, Complex.conj_conj]
  congr 2
  rw [show (↑n + 1 : ℂ) = ↑((n + 1 : ℕ) : ℕ) from by push_cast; ring,
    ← Complex.natCast_log, Complex.conj_ofReal]

