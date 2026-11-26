-- Prove2me | Theorems.Thm_section5_discretization_measurable
-- name    : section5_discretization_measurable
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:42.537663+00:00
-- url     : https://prove2.me/theorems/9a1a41f4-7ecf-4821-a0af-f1fb80c7618c
-- title:
--   Measurability of the squared threshold rounding discrepancy
-- statement:
--   For a natural grid parameter $M$, set $\Delta_M=\sqrt{4\pi/M}$, $R_M=M\Delta_M/2$, and $r_M(t)=-R_M+\Delta_M\lfloor(t+R_M)/\Delta_M\rfloor$. For $w\in\mathbb R^n$, let $f_w(x)=\operatorname{sgn}(\langle w,x\rangle)$, with the sign at zero equal to $1$. For arbitrary natural numbers $n,M$ and any $w\in\mathbb R^n$, let $r_M$ act coordinatewise. Then
--
--   $$
--   x\longmapsto\bigl(f_w(x)-f_w(r_M(x))\bigr)^2
--   $$
--
--   is measurable on Euclidean $\mathbb R^n$.
--
--   This permits integration of the squared rounding discrepancy, including the degenerate grid parameter under the formal definitions.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GaussianRounding.lean, section5_discretization_measurable, lines 115–133.

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example

theorem section5_discretization_measurable {n M : ℕ}
    (w : EuclideanSpace ℝ (Fin n)) :
    Measurable (fun x => (((ltf w 0 x-ltf w 0 (roundVec M x):ℤ):ℝ)^2)) := by sorry
