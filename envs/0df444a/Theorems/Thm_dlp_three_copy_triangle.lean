-- Prove2me | Theorems.Thm_dlp_three_copy_triangle
-- name    : dlp_three_copy_triangle
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:53:33.589084+00:00
-- url     : https://prove2.me/theorems/f401bbcb-e4c3-4904-afb7-fed45a9438e6
-- statement:
--   **de la Peña–Montgomery-Smith 1995 Lemma 1 (3-copy desymmetrization triangle).** On the product of three i.i.d. copies $\mu^3 = \mathrm{Measure.pi}\,(\lambda\_:\mathrm{Fin}\,3,\ \mu)$, with the three copies the coordinates $g_0,g_1,g_2$ and a Banach-valued measurable $f$, the single-copy tail is dominated by $3\times$ the i.i.d.-pair tail: $$\Pr[\,t\le\lVert f(g_0)\rVert\,]\ \le\ 3\,\Pr\!\big[\,\tfrac{2t}{3}\le\lVert f(g_0)+f(g_1)\rVert\,\big].$$ Proof: $2f(g_0) = (f(g_0)+f(g_1)) + (f(g_0)+f(g_2)) - (f(g_1)+f(g_2))$, so $t\le\lVert f(g_0)\rVert$ forces at least one of the three pair-sums to have norm $\ge 2t/3$ (union bound); the three pair-sum events are exchangeable (coordinate permutations of $\mu^3$ are measure-preserving since the factors are identical), so each has the same probability. This is the desymmetrization step (eq. (1)) of de la Peña–Montgomery-Smith's forward decoupling bound.
-- source:
--   de la Peña–Montgomery-Smith, *Decoupling Inequalities for the Tail Probabilities of Multivariate U-Statistics*, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), Lemma 1, p.807.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.Normed.Module.Basic
open MeasureTheory
open scoped ENNReal

theorem dlp_three_copy_triangle
    {α : Type*} [MeasurableSpace α]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
      [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → V) (hf : Measurable f) (t : ℝ) :
    (Measure.pi (fun _ : Fin 3 => μ)).real {g | t ≤ ‖f (g 0)‖}
      ≤ 3 * (Measure.pi (fun _ : Fin 3 => μ)).real
              {g | 2 * t / 3 ≤ ‖f (g 0) + f (g 1)‖} := by sorry
