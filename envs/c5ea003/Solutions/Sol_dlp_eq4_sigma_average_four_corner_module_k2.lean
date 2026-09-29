-- Prove2me | solution 1 for dlp_eq4_sigma_average_four_corner_module_k2
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T21:15:44.917441+00:00
-- url     : https://prove2.me/submissions/12794686-332e-4d79-a47d-deaf51e7e5e7

import Definitions.Def_dlp_sigma_randomization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module

open MatrixCompletion
open scoped BigOperators Classical

/-
de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4: after the eq-(4)
σ-randomization, the conditional expectation over the symmetric signs σ produces
`T_{n,k}` as the σ-AVERAGE of the four copy-corners (cf. /tmp/dlp.txt lines 405–444,
`T_{n,k} = 2^k Σ E(f(Z)|G₂)`).  At k = 2 this is the statement that the σ-average of
`4 • (the σ-decoupled corner) (copyPerm σ₁ l₁, copyPerm σ₂ l₂)` over the four sign
patterns `σ₁,σ₂ ∈ {±1}` reconstructs the FULL four-corner sum `∑_{j₁,j₂} f j₁ j₂`.

Pure module algebra (no measure theory; Module-generic so it specializes to
`RealMatrix`, which has no `NormedAddCommGroup` instance).  Each σ-pattern contributes
`∑_{j₁,j₂} (1+s(j₁,l₁)σ₁)(1+s(j₂,l₂)σ₂) • f j₁ j₂` by eq-(4); averaging the scalar
weight `(1+s σ₁)(1+s σ₂)` over σ₁,σ₂∈{±1} gives exactly `1` (the σ-linear and
σ-cross terms cancel), leaving `∑_{j₁,j₂} f j₁ j₂ = T_{n,2}`.

This is the bridge crossing (i) of the `9aaf089d` pair-core forward bound: it links the
σ-randomized decoupled corner to the full coupled four-corner `T_{n,2}`.
-/

theorem solution
    {M : Type*} [AddCommGroup M] [Module ℝ M]
    (l₁ l₂ : Fin 2) (f : Fin 2 → Fin 2 → M) :
    ((1 : ℝ) / 4) •
        (∑ σ₁ ∈ ({1, -1} : Finset ℝ), ∑ σ₂ ∈ ({1, -1} : Finset ℝ),
          ((4 : ℝ) • f (dlpCopyPerm σ₁ l₁) (dlpCopyPerm σ₂ l₂)))
      = ∑ j₁ : Fin 2, ∑ j₂ : Fin 2, f j₁ j₂ := by
  have hne : (1 : ℝ) ≠ -1 := by norm_num
  rw [Finset.sum_pair hne]
  simp only [Finset.sum_pair hne]
  -- expand the RHS four-corner sum and the σ-selected corners
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  -- average the four σ-selected corners; the σ-weights average to 1
  fin_cases l₁ <;> fin_cases l₂ <;>
    simp only [dlpCopyPerm, Fin.isValue, Fin.rev, Fin.mk_one,
      show ((-1:ℝ) = 1) = False by norm_num, if_true, if_false, reduceIte] <;>
    (try norm_num) <;> module

#print axioms solution
