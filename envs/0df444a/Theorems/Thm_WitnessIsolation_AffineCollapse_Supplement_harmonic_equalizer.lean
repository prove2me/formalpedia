-- Prove2me | Theorems.Thm_WitnessIsolation_AffineCollapse_Supplement_harmonic_equalizer
-- name    : WitnessIsolation.AffineCollapse.Supplement.harmonic_equalizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:48.540341+00:00
-- url     : https://prove2.me/theorems/954399ee-4b5d-4f1a-b561-a3d46c95a624
-- title:
--   Lemma 4.1 — Harmonic equalizer
-- statement:
--   Let $M\ge1$ and $H_M=\sum_{k=1}^M1/k$. Draw a nonempty set $A\subseteq[M]$ by choosing its size $k$ with probability $1/(kH_M)$ and then a uniform $k$-subset, i.e. from the harmonic subset law. These masses form a probability distribution, and for every nonempty $T\subseteq[M]$,
--   $$\Pr\bigl[\,|A\cap T|=1\,\bigr]=\frac1{H_M}.$$
--
--   The probability that the private set meets an arbitrary nonempty retained set in exactly one element does not depend on $T$. This is what lets the harmonic pool in the proof of Theorem 1.3 turn any general success guarantee above $1/H_M$ into a distinguisher.
--
--   Differences from the source:
--   - encoding: a two-stage random draw of A → a Law on Finset (Fin M) whose masses equal harmonicMass, with its existence (normalization) asserted; reason: the two-stage draw has exactly these masses; normalization is proved rather than assumed
--   - encoding: [M] = {1,…,M} → Fin M = {0,…,M−1}; reason: a relabelling of the ground set; no instance changes
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 8, PDF p. 9, Lemma 4.1; proof p. 9, PDF p. 10

import Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_harmonic

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- Lemma 4.1 (Harmonic equalizer), printed p. 8 / PDF p. 9. For every `M ≥ 1` the
two-stage harmonic masses form a probability law on subsets of `Fin M`, and for every
nonempty `T` the drawn set meets `T` in exactly one element with probability `1/H_M`. -/
theorem harmonic_equalizer (M : ℕ) (hM : 1 ≤ M) :
    ∃ μ : Law (Finset (Fin M)),
      (∀ A, μ.mass A = harmonicMass M A) ∧
      ∀ T : Finset (Fin M), T.Nonempty →
        μ.prob (fun A => (A ∩ T).card = 1) = 1 / (harmonic M : ℝ) := by sorry

end WitnessIsolation.AffineCollapse.Supplement
