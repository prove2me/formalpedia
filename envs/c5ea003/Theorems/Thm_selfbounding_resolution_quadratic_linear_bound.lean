-- Prove2me | Theorems.Thm_selfbounding_resolution_quadratic_linear_bound
-- name    : selfbounding_resolution_quadratic_linear_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T22:20:37.242073+00:00
-- url     : https://prove2.me/theorems/e591e0de-a6d8-4c53-a1be-e6a69d96fd17
-- title:
--   Self-bounding algebra: $EZ\le CA_0+CA_0\sqrt{EZ}\Rightarrow EZ\le 4(C+C^2)A_0$
-- statement:
--   Self-bounding desymmetrization algebra. If a nonnegative quantity $EZ$ satisfies the self-bounding recursion $EZ \le C\,A_0 + C\,A_0\sqrt{EZ}$ with $C\ge 0$, $0\le A_0\le 1$, then it linearises to $EZ \le 4(C+C^2)\,A_0$. This is the elementary quadratic-formula resolution of the recursion arising in Rudelson's selection theorem, where $A_0=\sqrt{\log d/p}\,\max_i\|y_i\|$ is the right-hand-side quantity that Candes-Recht 2009 Theorem 4.2(1) / eq.(4.9) requires to be $<1$ (encoded here as $A_0\le 1$). Writing $x=\sqrt{EZ}$, the hypothesis is $x^2\le CA_0(1+x)$; under $A_0\le 1$ a short case split ($x\le 2C$ vs $x>2C$) gives $x^2\le 4(C+C^2)A_0$.
-- source:
--   Candes & Recht, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, sec 4.2 eq.(4.9) p.18; Rudelson, Random vectors in the isotropic position, J. Funct. Anal. 164 (1999).

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
open Real

theorem selfbounding_resolution_quadratic_linear_bound :
    ∀ (EZ C A0 : ℝ), 0 ≤ EZ → 0 ≤ C → 0 ≤ A0 → A0 ≤ 1 →
      EZ ≤ C * A0 + C * A0 * Real.sqrt EZ →
      EZ ≤ 4 * (C + C ^ 2) * A0 := by sorry
