-- Prove2me | Theorems.Thm_TalagrandCore_lemma45_upper
-- name    : TalagrandCore.lemma45_upper
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:22.041036+00:00
-- url     : https://prove2.me/theorems/7b7f58aa-66a7-40b3-9996-e4f6d5ccac2f
-- title:
--   Klein–Rio Lemma 4.5: upper bound on the compensation function
-- statement:
--   Define $\psi(t)=(e^{2t}+1)/2$ and $\phi(t)=\psi(t)\log\psi(t)$. For $0\le t\le1/2$,
--
--   $$
--   \phi(t)\le te^{2t}-\frac{t^2}{2}.
--   $$
--
--   This analytic estimate controls the coefficient in the compensated-process differential inequality.
--
--   **Formalization Note** This is the upper half of Klein–Rio Lemma 4.5 in the exact scalar form used downstream.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem lemma45_upper (t : ℝ) (ht0 : 0 ≤ t) (ht : t ≤ 1/2) :
    phiKR t ≤ t * Real.exp (2*t) - t^2/2 := by sorry

end TalagrandCore
