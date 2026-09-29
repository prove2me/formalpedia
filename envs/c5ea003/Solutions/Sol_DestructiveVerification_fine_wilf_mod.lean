-- Prove2me | solution 1 for DestructiveVerification.fine_wilf_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:47:17.085523+00:00
-- url     : https://prove2.me/submissions/07b54eca-0019-47f9-ab5c-500ad039bfd8

-- Sol generated from Combinatorics/DestructiveVerificationIndistinguishability.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_eq_mod_period
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




/-! ## 3. A distinguishing delay: watching is necessary -/




open DestructiveVerification in
theorem solution{α : Type*} (s : ℕ → α) {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hper_p : ∀ m, s (m + p) = s m)
    (hper_q : ∀ k, k + q < p + q - Nat.gcd p q → s (k + q) = s k) :
    ∀ m, s m = s (m % Nat.gcd p q) := by
  set g := Nat.gcd p q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left q hp
  have hgp : g ≤ p := Nat.le_of_dvd hp (Nat.gcd_dvd_left p q)
  have hgq : g ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_right p q)
  set L := p + q - g with hL
  set w := (List.range L).map s with hw
  have hlen : w.length = L := by simp [hw]
  have hget : ∀ i, i < L → w[i]? = some (s i) := by
    intro i hi
    simp [hw, hi]
  have hP : List.HasPeriod w p := by
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    rw [hlen] at hi
    rw [hget i (by omega), hget (i + p) (by omega), hper_p i]
  have hQ : List.HasPeriod w q := by
    rw [List.hasPeriod_iff_getElem?]
    intro i hi
    rw [hlen] at hi
    rw [hget i (by omega), hget (i + q) (by omega), hper_q i (by omega)]
  have hG : List.HasPeriod w g := hP.gcd hQ (by rw [hlen])
  have hstep : ∀ i, i + g < L → s (i + g) = s i := by
    intro i hi
    rw [List.hasPeriod_iff_getElem?] at hG
    have hgi := hG i (by rw [hlen]; omega)
    rw [hget i (by omega), hget (i + g) (by omega)] at hgi
    exact (Option.some_inj.mp hgi).symm
  have hsmall : ∀ k, k < p → s k = s (k % g) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkg : k < g
      · rw [Nat.mod_eq_of_lt hkg]
      · push_neg at hkg
        have hkgg : k - g + g = k := by omega
        have h1 : s k = s (k - g) := by
          conv_lhs => rw [← hkgg]
          exact hstep (k - g) (by omega)
        rw [h1, ih (k - g) (by omega) (by omega), Nat.mod_eq_sub_mod hkg]
  intro m
  have h1 : s m = s (m % p) := eq_mod_period s hp hper_p m
  have h2 : s (m % p) = s ((m % p) % g) := hsmall (m % p) (Nat.mod_lt _ hp)
  rw [h1, h2, Nat.mod_mod_of_dvd m (Nat.gcd_dvd_left p q)]
