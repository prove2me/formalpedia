-- Prove2me | Theorems.Thm_CouretOaiBridge01_isBigO_comp_continuousLinearEquiv_iff
-- name    : CouretOaiBridge01.isBigO_comp_continuousLinearEquiv_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:46:32.443426+00:00
-- url     : https://prove2.me/theorems/b542639e-a1a1-4fd5-9e66-7aac10a2f722
-- title:
--   A continuous linear equivalence preserves Big-O
-- statement:
--   Let K be a nontrivially normed field, E a seminormed additive group and normed K-space, G a seminormed additive group, alpha any type, e:E→E a continuous linear equivalence, F:alpha→E, g:alpha→G and l any filter on alpha. Then $$(x\mapsto e(F(x)))=O_l(g)\iff F=O_l(g).$$ No finite-dimensional or nontrivial-filter premise is imposed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_A0_GenericNoGain.lean#L25-L45, lines 25–45; source file SHA-256 b264e6cd02b15c7dbdfaccd197fe24c72f5f0b2a1193340f20f0972cf344b2ce; theorem CouretOaiBridge01.isBigO_comp_continuousLinearEquiv_iff

import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Analysis.Normed.Operator.Asymptotics

open Filter
open Asymptotics

/-!
# COURET–OAI–BRIDGE–01 / A0 — Generic no-gain under a continuous linear equivalence

This file isolates the functional-analytic core of the fixed-modulus no-gain statement.
It is intentionally independent of U(30), Möbius sums, Dirichlet characters, and Mellin
transforms.

A continuous linear equivalence and its inverse are both bounded. Consequently, composing
a family with such an equivalence preserves its Big-O class.

Research status:
* exact abstract theorem;
* no Riemann-hypothesis claim;
* no novelty claim;
* intended as the zero-sorry base layer for BRIDGE01-A.
-/

namespace CouretOaiBridge01

theorem isBigO_comp_continuousLinearEquiv_iff
    {𝕜 E G α : Type*}
    [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup G]
    (e : E ≃L[𝕜] E)
    (F : α → E)
    (g : α → G)
    (l : Filter α) :
    (fun x => e (F x)) =O[l] g ↔ F =O[l] g := by sorry


end CouretOaiBridge01
