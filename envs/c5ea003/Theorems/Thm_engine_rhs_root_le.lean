-- Prove2me | Theorems.Thm_engine_rhs_root_le
-- name    : engine_rhs_root_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:40:44.186731+00:00
-- url     : https://prove2.me/theorems/72796e85-5931-478d-bcd2-df2129b27d7d
-- statement:
--   **Trace-moment engine RHS root + window collapse.** Taking the Hermitian trace-moment engine bound $\big(\tfrac{(2n)!}{2^n n!}\big)\,\text{normV}^n\, d$ to the $1/(2n)$ power and absorbing the dimension factor gives $\le \sqrt{2n}\cdot e\cdot\sqrt{\text{normV}}$, provided $2n \ge \log d$. This is the step turning the engine output into the $(C\sqrt{q}\cdot\text{rSVS})$-shaped Schatten moment bound (here $q = 2n$, $\sqrt{\text{normV}} = \text{rSVS}$). Proof (reduction): the central double-factorial quotient satisfies $\tfrac{(2n)!}{2^n n!} \le (2n)^n$ so its $1/(2n)$-root is $\le \sqrt{2n}$; $(\text{normV}^n)^{1/(2n)} = \sqrt{\text{normV}}$; and $d^{1/(2n)} \le e$ by the window lemma $N^{1/q} \le e$ for $q \ge \log N$.
-- source:
--   Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1. The constant-and-window step converting the Hermitian trace-moment engine output ((2n)!/(2ⁿn!)·normV^n·d) into a (C·√q·rSVS)-shaped Schatten moment bound (q = 2n, √normV = sampled variance scale): double-factorial (2n)!/(2ⁿn!) ≤ (2n)ⁿ ⇒ dblfact^{1/2n} ≤ √(2n), and the dimension factor d^{1/2n} ≤ e is absorbed by the window q ≥ log d.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
open scoped BigOperators

theorem engine_rhs_root_le (n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (normV : ℝ) (hV : 0 ≤ normV) (hlog : Real.log (d : ℝ) ≤ (2 * n : ℕ)) : Real.rpow (((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ))) * normV ^ n * (d : ℝ)) ((1 : ℝ) / (2 * n)) ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * Real.sqrt normV := by sorry
