-- Prove2me | Theorems.Thm_mme_MMObj_cyclic_tau_value
-- name    : mme_MMObj_cyclic_tau_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:11:18.475433+00:00
-- url     : https://prove2.me/theorems/cb7a56e1-06d6-4c7a-b320-30279b916960
-- title:
--   Exact elementary tau-value of a cyclic matrix-multiplication tensor
-- statement:
--   For any field $K$, dimensions $n,m,p$, and real parameter $\tau$, the cyclic symmetrization of $\langle n,m,p\rangle$ has tau-value at least the elementary weight of the square tensor of side length $nmp$:
--
--   $$
--   V_\tau\!\left(\operatorname{cyc}(\langle n,m,p\rangle)\right)\ge ((nmp)^3)^\tau.
--   $$
--
--   This is the exact rectangular-factor value used for the elementary entries of the Davie--Stothers exceptional $\Phi_{233}$ profile.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), elementary matrix-multiplication factors in Lemma 5.1(v), pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_tau_value
import Theorems.Thm_mme_HasTauValueAtLeast_mono_restrict

open MME

universe u

set_option autoImplicit false

theorem mme_MMObj_cyclic_tau_value
    {K : Type u} [Field K] (n m p : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (cyclicSymmetrization (MMObj K n m p)) tau
      ((((n * m * p) * (n * m * p) * (n * m * p) : ℕ) : ℝ) ^ tau) := by
  sorry
