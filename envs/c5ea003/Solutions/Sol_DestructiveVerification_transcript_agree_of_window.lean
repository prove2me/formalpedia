-- Prove2me | solution 1 for DestructiveVerification.transcript_agree_of_window
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:49:21.435331+00:00
-- url     : https://prove2.me/submissions/1f2bf7d2-6e7e-4992-ad5b-18f435bb588f

-- Sol generated from Combinatorics/DestructiveVerificationIndistinguishability.lean
import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
import Definitions.Def_Combinatorics_DestructiveVerificationDepth
import Definitions.Def_Combinatorics_DestructiveVerificationIndistinguishability
import Definitions.Def_Combinatorics_DestructiveVerificationRealization
import Theorems.Thm_DestructiveVerification_fine_wilf_mod
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
theorem solution(t : Test D) (d e : D) {i₁ p₁ i₂ p₂ T : ℕ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hper₁ : ∀ m, i₁ ≤ m → transcript t d (m + p₁) = transcript t d m)
    (hper₂ : ∀ m, i₂ ≤ m → transcript t e (m + p₂) = transcript t e m)
    (hT : max i₁ i₂ + p₁ + p₂ - Nat.gcd p₁ p₂ ≤ T)
    (h : ∀ j < T, transcript t d j = transcript t e j) (m : ℕ) :
    transcript t d m = transcript t e m := by
  set g := Nat.gcd p₁ p₂ with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left p₂ hp₁
  have hgp₁ : g ≤ p₁ := Nat.le_of_dvd hp₁ (Nat.gcd_dvd_left p₁ p₂)
  have hgp₂ : g ≤ p₂ := Nat.le_of_dvd hp₂ (Nat.gcd_dvd_right p₁ p₂)
  set I := max i₁ i₂ with hI
  set s : ℕ → Bool := fun k => transcript t d (I + k) with hs
  set s' : ℕ → Bool := fun k => transcript t e (I + k) with hs'
  have hsp : ∀ k, s (k + p₁) = s k := by
    intro k
    have hik : I + (k + p₁) = (I + k) + p₁ := by omega
    simp only [hs, hik]
    exact hper₁ (I + k) (by omega)
  have hs'p : ∀ k, s' (k + p₂) = s' k := by
    intro k
    have hik : I + (k + p₂) = (I + k) + p₂ := by omega
    simp only [hs', hik]
    exact hper₂ (I + k) (by omega)
  have hagree : ∀ k, I + k < T → s k = s' k := fun k hk => h (I + k) hk
  have hsq : ∀ k, k + p₂ < p₁ + p₂ - g → s (k + p₂) = s k := by
    intro k hk
    have h1 : s (k + p₂) = s' (k + p₂) := hagree _ (by omega)
    have h2 : s' (k + p₂) = s' k := hs'p k
    have h3 : s' k = s k := (hagree k (by omega)).symm
    rw [h1, h2, h3]
  have hs'q : ∀ k, k + p₁ < p₂ + p₁ - Nat.gcd p₂ p₁ → s' (k + p₁) = s' k := by
    intro k hk
    rw [Nat.gcd_comm p₂ p₁] at hk
    have h1 : s' (k + p₁) = s (k + p₁) := (hagree _ (by omega)).symm
    have h2 : s (k + p₁) = s k := hsp k
    have h3 : s k = s' k := hagree k (by omega)
    rw [h1, h2, h3]
  have hsg := fine_wilf_mod s hp₁ hp₂ hsp hsq
  have hs'g := fine_wilf_mod s' hp₂ hp₁ hs'p hs'q
  rw [Nat.gcd_comm p₂ p₁] at hs'g
  by_cases hm : m < I
  · exact h m (by omega)
  · push_neg at hm
    have hmod : (m - I) % g < g := Nat.mod_lt _ hg0
    have hwin : I + (m - I) % g < I + p₁ + p₂ - g := by omega
    have hkey : s (m - I) = s' (m - I) := by
      rw [hsg (m - I), hs'g (m - I)]
      exact hagree _ (lt_of_lt_of_le hwin hT)
    have hmI' : I + (m - I) = m := by omega
    have e1 : transcript t d m = s (m - I) := by simp only [hs]; rw [hmI']
    have e2 : transcript t e m = s' (m - I) := by simp only [hs']; rw [hmI']
    rw [e1, e2, hkey]
