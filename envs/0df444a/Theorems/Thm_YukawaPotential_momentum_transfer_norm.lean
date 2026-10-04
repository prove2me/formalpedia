-- Prove2me | Theorems.Thm_YukawaPotential_momentum_transfer_norm
-- name    : YukawaPotential.momentum_transfer_norm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-03T14:23:48.9048+00:00
-- url     : https://prove2.me/theorems/31008354-742b-4511-8918-0d1aa2521d64
-- title:
--   Momentum transfer for elastic scattering: $|\vec p-\vec p'| = 2p\sin(\theta/2)$
-- statement:
--   Let $\vec p,\vec p'\in\mathbb R^3$ have the same length $|\vec p|=|\vec p'|=p$, and let $\theta\in[0,\pi]$ be the angle between them. Then
--   $$|\vec p-\vec p'| = 2p\,\sin\!\bigl(\tfrac12\theta\bigr).$$
--
--   This is the kinematic identity used in the section *Cross section* after energy conservation forces $|\vec p|=|\vec p'|$.
--
--   **Formalization Note** The angle is Mathlib's `InnerProductGeometry.angle`, i.e. $\arccos\bigl(\langle\vec p,\vec p'\rangle/(|\vec p||\vec p'|)\bigr)$; when $p=0$ this convention gives $\pi/2$ and both sides are $0$.
-- source:
--   Wikipedia, "Yukawa potential", revision oldid=1371658231, https://en.wikipedia.org/w/index.php?title=Yukawa_potential&oldid=1371658231, section 'Cross section': energy conservation implies |p| = |p'| = p, so that |p - p'| = 2p sin(θ/2).

import Mathlib
import Definitions.Def_YukawaPotential_Defs

open MeasureTheory Filter Topology

namespace YukawaPotential
theorem momentum_transfer_norm (p : ℝ) (P P' : EuclideanSpace ℝ (Fin 3))
    (hP : ‖P‖ = p) (hP' : ‖P'‖ = p) :
    ‖P - P'‖ = 2 * p * Real.sin (InnerProductGeometry.angle P P' / 2) := by sorry
end YukawaPotential
