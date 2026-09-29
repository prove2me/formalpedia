-- Prove2me | Theorems.Thm_bernstein_exp_le
-- name    : bernstein_exp_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T23:43:28.69982+00:00
-- url     : https://prove2.me/theorems/5e6a26cb-e2bc-4caa-b660-5f5a4bf57bc7
-- title:
--   Bernstein's exponential lemma: $e^\lambda-1-\lambda\le\frac{\lambda^2}{2(1-\lambda/3)}$
-- statement:
--   Bernstein's exponential lemma (BLM *Concentration Inequalities* eq (2.10); Klein–Rio 2005 / Bousquet 2002): for $0 \le \lambda < 3$, $e^{\lambda}-1-\lambda \le \dfrac{\lambda^2}{2(1-\lambda/3)}$. The scalar core that gives the sub-gamma / Bennett–Bernstein exponent shape.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013) §2.4 eq (2.10); Klein–Rio 2005 Ann.Probab.33 (arXiv:math/0506594); Bousquet 2002 C.R.Acad.Sci.334:495-500.

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic
open Real Set

theorem bernstein_exp_le (lam : ℝ) (h0 : 0 ≤ lam) (h3 : lam < 3) :
    Real.exp lam - 1 - lam ≤ lam ^ 2 / (2 * (1 - lam / 3)) := by sorry
