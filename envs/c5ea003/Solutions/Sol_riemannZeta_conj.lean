-- Prove2me | solution 1 for riemannZeta_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T19:39:48.614473+00:00
-- url     : https://prove2.me/submissions/da798fb8-92a1-4fe1-be4a-bdfc85fbc1dd

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Theorems.Thm_conj_riemannZeta_conj

open scoped Complex ComplexConjugate

theorem solution (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rw [← conj_riemannZeta_conj, Complex.conj_conj]

