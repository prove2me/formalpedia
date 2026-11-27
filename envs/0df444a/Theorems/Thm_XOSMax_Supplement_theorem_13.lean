-- Prove2me | Theorems.Thm_XOSMax_Supplement_theorem_13
-- name    : XOSMax.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:38:10.442429+00:00
-- url     : https://prove2.me/theorems/74cb64b5-1b60-550f-b469-49ae75082958
-- title:
--   Theorem 13 — exact maximization under condition $(*)$ in $O(n^{k+1})$
-- statement:
--   One deterministic value-oracle algorithm, constructed from the ground enumeration and not given $k$, exactly maximizes every $k$-XOS function having a representation satisfying condition $(*)$. For every $k\ge2$ there is $C$ such that its charged cost is at most
--   $$
--   Cn^{k+1}.
--   $$
--   The algorithm includes the Section 2 preprocessing, so the theorem has no singleton-positivity hypothesis.
--
--   Differences from the source:
--   - encoding: a $k$-XOS function with condition $(*)$ → a signed width-$k$ representation satisfying `Represents` and `ConditionStar`; reason: condition $(*)$ refers to the representation's clauses, while the algorithm is chosen before and does not receive that representation
--   - encoding: deterministic algorithm running in $O(n^{k+1})$ → an oracle program fixed before $k$ and $f$, with a constant depending only on $k$ and a bound on charged cost; reason: this makes "even if $k$ is unknown" and the asymptotic uniformity explicit
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, Theorem 13, pp.8-9

import Mathlib
import Definitions.Def_XOSMax_Represents
import Definitions.Def_XOSMax_IsMaximizerApprox
import Definitions.Def_XOSMax_OracleProg
import Definitions.Def_XOSMax_Supplement_ConditionStar

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- **Theorem 13.** One deterministic algorithm, without knowing `k`, exactly maximizes every
`k`-XOS function having a representation satisfying `(∗)` in `O(n^(k+1))` time
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, Theorem 13, pp.8–9).

**Formalization Note** The program is fixed from the ground enumeration before `k`, the
representation, and the oracle. It incorporates §2 preprocessing, hence no singleton-positivity
hypothesis appears. The representation is existential data of the input property, but is not an
argument to the program. The running-time constant may depend on `k` only. -/
theorem theorem_13 :
    ∀ (E : Type) [Fintype E] [DecidableEq E] [Nonempty E] (L : List E),
      L.Nodup → L.toFinset = Finset.univ →
      ∃ A : OracleProg E (Finset E), ∀ k : ℕ, 2 ≤ k →
        ∃ C : ℕ, 0 < C ∧ ∀ (w : Fin k → E → ℝ) (f : Finset E → ℝ),
          Represents w f → ConditionStar w f →
          IsMaximizerApprox Finset.univ 1 f (run f A).1 ∧
          (run f A).2 ≤ C * Fintype.card E ^ (k + 1) := by sorry

end XOSMax.Supplement
