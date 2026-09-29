-- Prove2me | Theorems.Thm_mme_MMObj_one_middle_one_tau_value
-- name    : mme_MMObj_one_middle_one_tau_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:16:59.637315+00:00
-- url     : https://prove2.me/theorems/a05e8bda-8800-42d4-9fd2-46e5538cae0f
-- title:
--   Exact tau-value of the matrix tensor $\langle 1,r,1\rangle$
-- statement:
--   Let $K$ be a field, let $r$ be a nonnegative integer, and let $\tau$ be real. The literal matrix-multiplication tensor $\langle 1,r,1\rangle$ has tau-value at least
--
--   $$
--   r^{\tau}.
--   $$
--
--   At every power $N$, its Kronecker power is canonically isomorphic to $\langle 1,r^N,1\rangle$, which gives a one-summand finite extraction of exact tau-weight $(r^N)^{\tau}=(r^{\tau})^N$. This is the exact matrix-tensor value needed for the $(2,2,0)$ constituent, not a dimension-only proxy.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and Lemma 4.6(b), specialized to the matrix-multiplication constituent used in Section 6.3 and Equation (25), PDF pp. 13, 32-33, and 59-60; https://arxiv.org/abs/2210.10173.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_kronFin_MMObj_iso

open Filter BigOperators
open MME

set_option autoImplicit false

universe u

theorem mme_MMObj_one_middle_one_tau_value
    {K : Type u} [Field K]
    (r : ℕ) (tau : ℝ) :
    HasTauValueAtLeast (MMObj K 1 r 1) tau (Real.rpow r tau) := by sorry
