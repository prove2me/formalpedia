-- Prove2me | Theorems.Thm_AbelianTargets_familyCurve_joint
-- name    : AbelianTargets.familyCurve_joint
-- status  : Proved
-- author  : @username
-- created : 2026-10-19T03:42:25.678829+00:00
-- url     : https://prove2.me/theorems/b5ae5018-fdd4-46b4-a269-6491bd9f1e00
-- title:
--   Finite equal-slot concatenations of jointly Lipschitz curve families are jointly Lipschitz
-- statement:
--   Let $X,Y$ be metric spaces and let $H_j:X\times I\to Y$ be maps for $j\in\mathbb N$, with exact seams
--   $$H_j(x,1)=H_{j+1}(x,0)\qquad(j\in\mathbb N,\ x\in X).$$
--   Suppose each $H_j$ has some finite joint Lipschitz bound, using the maximum product metric. For each $n\in\mathbb N$, concatenate $H_0,\ldots,H_{n-1}$ into $n$ equal time slots, clamped outside $[0,1]$, to obtain $C_n:\mathbb R\times X\to Y$; define $C_0(t,x)=H_0(x,0)$. Then
--   $$\forall n\in\mathbb N\ \exists J_n\ge0,\quad \operatorname{Lip}(C_n)\le J_n.$$
--   No uniform bound in $j$ or $n$ is assumed or concluded.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (30 September 2026), Sections 2–7, supporting construction for Theorem 1.4 and Proposition 7.1; https://arxiv.org/html/2609.39824v1. Formalization-specific helper: AbelianTargets/CurveFamilyStages.lean, lines 74–113; SHA256 90bffa2ab1a52975c548436151b65b89efbd876cc18f62f75a0e1c6f8691283c.

import Definitions.Def_AT260939824_CurveFamilyStages
import Definitions.Def_AT260939824_RelativePathContraction
import Init
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Homotopy.Path
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

/-! Equal-slot concatenation of a family of curves with literal seams. -/
namespace AbelianTargets
end AbelianTargets
open AbelianTargets
open scoped NNReal unitInterval

theorem AbelianTargets.familyCurve_joint {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (H : ℕ → X × I → Y) (hseam : ∀ n x, H n (x,1)=H (n+1) (x,0))
    (hjoint : ∀ n, ∃ J : ℝ≥0, LipschitzWith J (H n)) (n : ℕ) :
    ∃ J : ℝ≥0, LipschitzWith J (familyCurve H n) := by sorry
