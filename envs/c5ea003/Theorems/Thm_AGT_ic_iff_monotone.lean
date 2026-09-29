-- Prove2me | Theorems.Thm_AGT_ic_iff_monotone
-- name    : AGT.ic_iff_monotone
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:36:28.396579+00:00
-- url     : https://prove2.me/theorems/a8481e90-a1c5-4c50-ad63-ba3b296d5175
-- title:
--   Incentive compatibility is equivalent to monotonicity
-- statement:
--   A social choice function is incentive compatible if and only if it is monotone (Proposition 9.6 of *Algorithmic Game Theory*). Incentive compatibility says no voter can move the outcome to one they strictly prefer (under their true preference) by misreporting; monotonicity says that when a single voter's change of vote moves the outcome from $a$ to $a' \ne a$, that voter ranked $a$ above $a'$ in the old vote and $a'$ above $a$ in the new one. The two properties quantify over the same data — a profile, a voter, an alternate vote — and the book calls the equivalence "a more combinatorial point of view" of strategyproofness.
--
--   *A note on the rendering.* No finiteness, cardinality, or nonemptiness assumptions appear: the equivalence is pure quantifier rearrangement and holds for arbitrary sets of voters and alternatives.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.2.4, Proposition 9.6, p. 213

import Definitions.Def_agt_social

namespace AGT

/-- **Proposition 9.6 of *Algorithmic Game Theory***: a social choice
function is incentive compatible if and only if it is monotone.  The two
notions quantify over the same data — a profile, a voter, and an alternate
vote — and the proposition is the book's "combinatorial point of view" on
strategyproofness; no finiteness or cardinality assumptions are needed. -/
theorem ic_iff_monotone {A ι : Type*} [DecidableEq ι]
    (f : (ι → A → A → Prop) → A) :
    IncentiveCompatible f ↔ SCFMonotone f := by
  sorry

end AGT
