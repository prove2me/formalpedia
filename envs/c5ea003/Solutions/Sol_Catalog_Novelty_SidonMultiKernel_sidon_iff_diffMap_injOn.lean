-- Prove2me | solution 1 for Catalog.Novelty.SidonMultiKernel.sidon_iff_diffMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:32.819978+00:00
-- url     : https://prove2.me/submissions/c842b9b3-6882-4167-91ea-c584fa9081ce

-- Sol generated from Novelty/DifferenceKernel.lean
import Mathlib
import Definitions.Def_Novelty_DifferenceKernel
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sidon sets: the difference kernel, its exact cardinality, and a sharp characterisation

A finite set of integers `s` is a **Sidon set** (a `B₂` set) when all of its
pairwise sums are distinct.  Companion catalog work analyses the *sum* kernel
`r⁺_s = 1_s * 1_s` (representation function, additive energy, sumset size).
This file develops the complementary **difference kernel** `r⁻_s(x) = #{(a,b) ∈
s² : a - b = x}`, i.e. the correlation `1_s ⋆ 1_s`.

The two convolution kernels `r⁺` and `r⁻` are the "multi-kernel" pair whose
combined support governs the additive structure of `s`.  For a Sidon set the
difference kernel is as *spread out* as possible: every nonzero difference is
attained exactly once, so the difference set `s - s` attains the maximal
possible cardinality `|s|² - |s| + 1` (the `|s|²-|s|` ordered pairs of distinct
elements, all distinct, together with `0`).  Conversely, attaining this maximum
*characterises* Sidon sets.

## Main results

* `sidon_diff_card` — for a nonempty Sidon set, `|s - s| + |s| = |s|² + 1`,
  i.e. `|s - s| = |s|² - |s| + 1`.
* `sidon_iff_diff_card` — a nonempty set is Sidon **iff** its difference set has
  the maximal cardinality `|s - s| + |s| = |s|² + 1`.

## Tags
Sidon set, B₂ set, difference set, correlation kernel, additive combinatorics

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).**  The classical Sidon theory pins down the *sum*
side: for a Sidon set `2|s+s| = |s|(|s|+1)`.  We conjectured a dual statement
for the *difference* kernel: since a Sidon set has all pairwise differences
distinct, the difference set should have the maximal cardinality
`|s-s| = |s|²-|s|+1`, and — more strongly — this maximum should *characterise*
Sidon sets.

**Experiment (Experimenter).**  Direct computation on the power-of-two Sidon set
`{1,2,4,8}` (|s|=4): `|s+s| = 10`, `|s-s| = 13 = 16-4+1` ✓, while the
non-Sidon `{1,2,3,4}` gives `|s-s| = 7 < 13`.  The extremal gap confirmed the
"maximal difference set ⇔ Sidon" hypothesis.

**Analysis (Analyst).**  The whole phenomenon factors through a single
equivalence, `sidon_iff_diffMap_injOn`: `s` is Sidon iff the map `(a,b)↦a-b` is
injective on the off-diagonal.  From there the counts are pure `Finset`
bookkeeping (`card_image_of_injOn`, `offDiag_card`, `card_insert_of_notMem`).
Injectivity failed on the *whole* square (the diagonal always collapses to `0`),
which is why the statements are phrased on `offDiag` and `s` must be nonempty
(the empty set is vacuously Sidon but has `|s-s| = 0 ≠ 1`).

**Critique (Critic).**  Neither theorem is vacuous: the reverse direction of
`sidon_iff_diff_card` genuinely recovers the Sidon property from a cardinality
equation, and the proofs use `card_image_iff`, `offDiag_card` and `omega`, not
`decide`/`native_decide`.  The nonemptiness hypothesis is load-bearing and
minimal.

**Synthesis (PI).**  The difference kernel yields an exact cardinality *and* a
new characterisation, dual to the known sum-kernel results, and feeds the
sum/difference "multi-kernel" identity in `MultiKernelLaw.lean`.
-- !-- Lab Notes -- !--
-/

open Finset
open scoped Pointwise

open Catalog.Novelty.SidonMultiKernel











open Catalog.Novelty.SidonMultiKernel in
theorem solution(s : Finset ℤ) :
    IsSidon s ↔ Set.InjOn diffMap (s.offDiag : Set (ℤ × ℤ)) := by
  constructor
  · intro hs p hp q hq hpq
    rw [Finset.mem_coe, Finset.mem_offDiag] at hp hq
    obtain ⟨hp1, hp2, hpne⟩ := hp
    obtain ⟨hq1, hq2, hqne⟩ := hq
    simp only [diffMap] at hpq
    have key : p.1 + q.2 = p.2 + q.1 := by linarith
    rcases hs p.1 hp1 q.2 hq2 p.2 hp2 q.1 hq1 key with h | h
    · exact absurd h hpne
    · have : p.2 = q.2 := by linarith
      exact Prod.ext h this
  · intro hinj a ha b hb c hc d hd hsum
    by_cases had : a = d
    · exact Or.inr had
    · by_cases hcb : c = b
      · right; linarith
      · left
        have hp : (a, d) ∈ (s.offDiag : Set (ℤ × ℤ)) := by
          rw [Finset.mem_coe, Finset.mem_offDiag]; exact ⟨ha, hd, had⟩
        have hq : (c, b) ∈ (s.offDiag : Set (ℤ × ℤ)) := by
          rw [Finset.mem_coe, Finset.mem_offDiag]; exact ⟨hc, hb, hcb⟩
        have hd2 : diffMap (a, d) = diffMap (c, b) := by
          simp only [diffMap]; linarith
        have := hinj hp hq hd2
        exact (Prod.ext_iff.mp this).1
