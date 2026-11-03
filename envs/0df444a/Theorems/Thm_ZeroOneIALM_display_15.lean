-- Prove2me | Theorems.Thm_ZeroOneIALM_display_15
-- name    : ZeroOneIALM.display_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:48.140725+00:00
-- url     : https://prove2.me/theorems/f1968fc1-b0cc-449c-bd5d-544eac46b735
-- title:
--   Display (15): the sign pattern of $u\in\mathrm{Prox}(u+\alpha z)$
-- statement:
--   Let $\lambda,\alpha>0$ and $u,z\in\mathbb R^n$. If $u\in\mathrm{Prox}_{\alpha\lambda\|(\cdot)_+\|_0}(u+\alpha z)$, then for every $i\in[n]$ one of the following holds:
--   $$
--   z_i=0,\quad u_i\in(-\infty,0]\cup[\sqrt{2\lambda\alpha},\infty),
--   $$
--   or
--   $$
--   u_i=0,\quad z_i\in[0,\sqrt{2\lambda/\alpha}].
--   $$
--
--   The paper derives this in the proof of Property 3 and uses it again as display (83), in the proof of Theorem 7.
--
--   Differences from the source: none.
-- source:
--   Zhang & Xiu, Global Convergence of Inexact Augmented Lagrangian Method for Zero-One Composite Optimization, arXiv:2112.00440v1, proof of Property 3, display (15), p.8; used as display (83), p.25

import Mathlib
import Definitions.Def_ZeroOneIALM_Prox

namespace ZeroOneIALM

/-- Display (15), proof of Property 3, Zhang & Xiu, arXiv:2112.00440v1, p.8 (used again as display
(83), p.25): if `u ∈ Prox_{αλ‖(·)₊‖₀}(u + αz)` then, in every coordinate, either `zᵢ = 0` and
`uᵢ ∈ (-∞, 0] ∪ [√(2λα), ∞)`, or `uᵢ = 0` and `zᵢ ∈ [0, √(2λ/α)]`. -/
theorem display_15 {n : ℕ} {lam α : ℝ} (hlam : 0 < lam) (hα : 0 < α)
    (u z : EuclideanSpace ℝ (Fin n)) (h : u ∈ proxVec lam α (u + α • z)) (i : Fin n) :
    (z i = 0 ∧ u i ∈ Set.Iic 0 ∪ Set.Ici (Real.sqrt (2 * lam * α))) ∨
      (u i = 0 ∧ z i ∈ Set.Icc 0 (Real.sqrt (2 * lam / α))) := by sorry

end ZeroOneIALM
