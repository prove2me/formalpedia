-- Prove2me | Theorems.Thm_AGT_arrow_theorem
-- name    : AGT.arrow_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:36:45.481718+00:00
-- url     : https://prove2.me/theorems/b1f96094-367a-4b61-815d-bf68446a6dd7
-- title:
--   Arrow's impossibility theorem
-- statement:
--   Aggregating rankings over three or more alternatives under unanimity and independence of irrelevant alternatives forces a dictator — Arrow's impossibility theorem (Theorem 9.3 of *Algorithmic Game Theory*). Let $A$ have more than two alternatives and let there be finitely many, and at least one, voters. Every social welfare function $F$ — every aggregator carrying preference profiles to social preferences that are again strict total orders — satisfying
--
--   1. **unanimity**: on each identical profile $(r, \dots, r)$ the social preference is $r$, and
--   2. **independence of irrelevant alternatives**: the social comparison of $a$ with $b$ depends only on the voters' comparisons of $a$ with $b$,
--
--   has a dictator: a voter $i$ such that on every profile the social preference coincides with $i$'s.
--
--   *A note on the hypotheses.* $\mathrm{Nonempty}\ \iota$ matches the book's setting of $n \ge 1$ voters; it is not needed for truth — with zero voters the identical-profile unanimity is already unsatisfiable over three or more alternatives (the empty profile would have to coincide with every strict total order at once), so that case is vacuous either way. Unanimity is the book's identical-profile form (Definition 9.2); combined with IIA it yields the pairwise form ("if all voters rank $a$ above $b$, so does society") that the proof uses. $|A| \ge 3$ enters as $2 < |A|$; with two alternatives majority rule is a counterexample, so the bound is sharp.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.2.3, Theorem 9.3, pp. 212-213

import Definitions.Def_agt_social

namespace AGT

/-- **Theorem 9.3 of *Algorithmic Game Theory* (Arrow)**: every social
welfare function over more than two alternatives that satisfies unanimity
and independence of irrelevant alternatives is a dictatorship.

`Nonempty ι` pins the statement to the book's setting of `n ≥ 1` voters.
(It is not needed for truth: with zero voters and `|A| ≥ 3` the
identical-profile unanimity below is already unsatisfiable — the empty
profile would have to agree simultaneously with every strict total
order — so that case is vacuous either way.)  Unanimity is the book's
identical-profile form (Definition 9.2); together with IIA it yields the
pairwise form used in the proof. -/
theorem arrow_theorem {A ι : Type*} [Fintype A] [Fintype ι] [Nonempty ι]
    (hA : 2 < Fintype.card A) (F : (ι → A → A → Prop) → A → A → Prop)
    (hF : IsSWF F) (huna : SWFUnanimity F) (hiia : SWFIIA F) :
    ∃ i : ι, SWFDictator F i := by
  sorry

end AGT
