-- Prove2me | Theorems.Thm_AGT_gibbard_satterthwaite
-- name    : AGT.gibbard_satterthwaite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:37:00.605915+00:00
-- url     : https://prove2.me/theorems/5d1392c0-bd93-4369-add3-8b8f2d6104a4
-- title:
--   The Gibbard-Satterthwaite theorem
-- statement:
--   Every incentive compatible voting rule onto three or more alternatives is a dictatorship — the Gibbard–Satterthwaite theorem (Theorem 9.8 of *Algorithmic Game Theory*), and this mission's goal. Let $A$ have more than two alternatives, finitely many voters, and let $f$ be a social choice function that is **incentive compatible** — no voter can move the outcome to one they strictly prefer by misreporting — and **onto** $A$ — every alternative is elected on some profile. Then $f$ is a dictatorship: some voter $i$ is such that whenever an alternative is $i$'s unique top choice, $f$ elects it.
--
--   *A note on the hypotheses.* Ontoness is essential, as the book stresses — without it the bound on $|A|$ has no bite (an incentive compatible function into a fixed pair of alternatives need not have a dictator). No nonemptiness of the voter set is assumed: with zero voters an onto function onto three or more alternatives cannot exist, so the statement holds vacuously, and adding the hypothesis would only weaken the theorem. The book derives the result from Arrow's theorem through the top-set extension (Definition 9.9, Lemmas 9.10–9.11); the formal statement fixes no proof route.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 9.2.4, Theorem 9.8, pp. 214-215

import Definitions.Def_agt_social

namespace AGT

/-- **Theorem 9.8 of *Algorithmic Game Theory* (Gibbard–Satterthwaite)**,
the capstone of the mission: every incentive compatible social choice
function onto more than two alternatives is a dictatorship.

The ontoness requirement is essential — without it the bound on `|A|` has no
bite (a function into a fixed pair of alternatives can be incentive
compatible without any dictator).  No `Nonempty ι` hypothesis is needed:
with no voters an onto function onto three or more alternatives cannot
exist, so the statement holds vacuously. -/
theorem gibbard_satterthwaite {A ι : Type*} [Fintype A] [Fintype ι]
    [DecidableEq ι] (hA : 2 < Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hic : IncentiveCompatible f)
    (honto : SCFOnto f) :
    ∃ i : ι, SCFDictator f i := by
  sorry

end AGT
