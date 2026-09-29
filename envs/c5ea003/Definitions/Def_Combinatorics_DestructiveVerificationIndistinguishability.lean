-- Prove2me | Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
-- name    : Combinatorics_DestructiveVerificationIndistinguishability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:34:15.12441+00:00
-- url     : https://prove2.me/theorems/c5d951bf-bedb-4911-b6c2-95b15046e6dd
-- title:
--   Aether Catalog definitions — Combinatorics_DestructiveVerificationIndistinguishability
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.DestructiveVerificationIndistinguishability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/DestructiveVerificationIndistinguishability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
/-
# Destructive verification IV: how many runs distinguish two dishes?

In the state-transition model of `Combinatorics.DestructiveVerification` a test
`t : D → Bool × D` can only be used by *running* it: the observer sees the
verdict stream (`transcript`) obtained by feeding the residue back in.  Two
dishes are **observationally equivalent** for `t` when their transcripts agree
at every step.  How long must one watch before equivalence is certain?

The naive answer, obtained by running the product dynamics on `D × D` and
applying the pigeonhole principle, is `#D ^ 2` runs.  The main theorem here
improves this to a **linear** bound:

* `DestructiveVerification.transcript_indistinguishable` — if the transcripts of
  two dishes agree for the first `2 * #D` runs, they agree forever; and
* `DestructiveVerification.indistinguishable_iff_prefix` — hence observational
  equivalence is *exactly* agreement on a prefix of length `2 * #D`.

The improvement is a genuine cross-domain bridge: the quadratic bound is what
dynamics on the product state space gives, while the linear bound comes from
**combinatorics on words** — the Fine–Wilf periodicity lemma
(`List.HasPeriod.gcd` in Mathlib).  Both transcripts are eventually periodic
with `preperiod + period ≤ #D` (that is the state-transition input); a window of
length `p + q` on which they agree forces the common word to have period
`gcd p q` (that is the word-combinatorial input), which pins the two streams
together forever.

Supporting general-purpose lemmas, stated for arbitrary streams:

* `DestructiveVerification.eq_mod_period` — a globally `p`-periodic stream is
  determined by its values on `[0, p)`;
* `DestructiveVerification.fine_wilf_mod` — a stream that is globally
  `p`-periodic and `q`-periodic on a window of length `p + q` is globally
  `gcd p q`-periodic.

Finally `DestructiveVerification.clock_distinguishing_delay` exhibits, on five
dishes, two dishes whose transcripts agree for three runs and disagree on the
fourth: watching is genuinely necessary, one run never suffices.
-/

namespace DestructiveVerification

variable {D : Type*}

/-! ## 1. Streams: periodicity toolkit -/



/-! ## 2. The distinguishing engine -/




/-! ## 3. A distinguishing delay: watching is necessary -/

/-- Five dishes: a two-cycle `{0,1}` and a three-cycle `{2,3,4}`, with verdicts
`true, false, true, false, true`.  Dishes `0` and `2` look identical for three
runs and part company on the fourth. -/
def clockTest : Test (Fin 5) :=
  fun j => (![true, false, true, false, true] j, ![1, 0, 3, 4, 2] j)


end DestructiveVerification


