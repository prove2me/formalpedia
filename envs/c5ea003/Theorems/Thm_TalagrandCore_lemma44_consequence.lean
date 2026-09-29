-- Prove2me | Theorems.Thm_TalagrandCore_lemma44_consequence
-- name    : TalagrandCore.lemma44_consequence
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-13T04:59:26.578133+00:00
-- url     : https://prove2.me/theorems/81b13639-2bdf-4ce2-9849-1851b8d02fec
-- title:
--   Klein–Rio Lemma 4.4: Bennett-kernel comparison
-- statement:
--   For $t>0$ and $y\le1$, the Bennett kernel obeys
--
--   $$
--   (ty-1)e^{ty}+1\le y^2\bigl(1+(t-1)e^t\bigr).
--   $$
--
--   This is the pointwise consequence of the monotonicity of $x^{-2}(1+(x-1)e^x)$ used in Klein–Rio’s lower-tail entropy argument.
--
--   **Formalization Note** The statement remains valid without a lower bound on $y$.
-- source:
--   T. Klein and E. Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2 and 4, pp. 1060–1077, arXiv:math/0506594. Formal Lean proof extracted from Prove2Me accepted submission bf106d23-ff42-48f5-a837-a8528101c849 by tianyipeng.

import Definitions.Def_talagrand_finite_bool_core
open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [Fintype ι] [Nonempty ι]

theorem lemma44_consequence (t y : ℝ) (ht : 0 < t) (hy : y ≤ 1) :
    (t*y - 1) * Real.exp (t*y) + 1 ≤ y^2 * (1 + (t - 1) * Real.exp t) := by sorry

end TalagrandCore
