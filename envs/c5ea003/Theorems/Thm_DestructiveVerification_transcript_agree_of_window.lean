-- Prove2me | Theorems.Thm_DestructiveVerification_transcript_agree_of_window
-- name    : DestructiveVerification.transcript_agree_of_window
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:11:15.89999+00:00
-- url     : https://prove2.me/theorems/83e95a96-04fd-4915-9dec-e42ca506ead6
-- title:
--   Distinguishing engine.
-- statement:
--   **Distinguishing engine.**  Suppose the two transcripts are eventually
--   periodic with preperiods `i₁, i₂` and periods `p₁, p₂`, and suppose they agree
--   on a prefix of length `T` where `T` covers the Fine–Wilf window
--   `max i₁ i₂ + p₁ + p₂ - gcd p₁ p₂`.  Then they agree everywhere.
--
--   All distinguishing bounds below are instances of this lemma; only the estimate
--   of the window changes.
--
--   ```lean
--   theorem DestructiveVerification.transcript_agree_of_window(t : Test D) (d e : D) {i₁ p₁ i₂ p₂ T : ℕ}
--       (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
--       (hper₁ : ∀ m, i₁ ≤ m → transcript t d (m + p₁) = transcript t d m)
--       (hper₂ : ∀ m, i₂ ≤ m → transcript t e (m + p₂) = transcript t e m)
--       (hT : max i₁ i₂ + p₁ + p₂ - Nat.gcd p₁ p₂ ≤ T)
--       (h : ∀ j < T, transcript t d j = transcript t e j) (m : ℕ) :
--       transcript t d m = transcript t e m := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/DestructiveVerificationIndistinguishability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/DestructiveVerificationIndistinguishability.lean#L119

-- Thm stub generated from Combinatorics/DestructiveVerificationIndistinguishability.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
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

open DestructiveVerification

variable {D : Type*}

/-! ## 1. Streams: periodicity toolkit -/



/-! ## 2. The distinguishing engine -/

theorem DestructiveVerification.transcript_agree_of_window(t : Test D) (d e : D) {i₁ p₁ i₂ p₂ T : ℕ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hper₁ : ∀ m, i₁ ≤ m → transcript t d (m + p₁) = transcript t d m)
    (hper₂ : ∀ m, i₂ ≤ m → transcript t e (m + p₂) = transcript t e m)
    (hT : max i₁ i₂ + p₁ + p₂ - Nat.gcd p₁ p₂ ≤ T)
    (h : ∀ j < T, transcript t d j = transcript t e j) (m : ℕ) :
    transcript t d m = transcript t e m := by sorry
