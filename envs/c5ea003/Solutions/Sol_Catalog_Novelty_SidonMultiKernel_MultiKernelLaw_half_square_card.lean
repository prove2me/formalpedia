-- Prove2me | solution 1 for Catalog.Novelty.SidonMultiKernel.MultiKernelLaw.half_square_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:31.969075+00:00
-- url     : https://prove2.me/submissions/0048b00a-23f5-49d6-a69c-acaaa237f519

-- Sol generated from Novelty/MultiKernelLaw.lean
import Mathlib
import Definitions.Def_Novelty_MultiKernelLaw
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sidon sets: the sum/difference multi-kernel conservation law

For a finite set `s ⊆ ℤ` there are two elementary vector-valued convolution
kernels attached to it: the **sum kernel** `r⁺_s(x) = #{(a,b) ∈ s² : a+b = x}`
(the self-convolution `1_s * 1_s`, supported on the sumset `s + s`) and the
**difference kernel** `r⁻_s(x) = #{(a,b) ∈ s² : a-b = x}` (the correlation
`1_s ⋆ 1_s`, supported on the difference set `s - s`).  The "multi-kernel
smoothing" programme studies weighted combinations of such kernels; the coarsest
invariant of any such combination is the size of the *support* of each kernel.

This file proves the two exact support counts for a Sidon set and combines them
into a single **conservation law** relating the two kernels:

`2·|s + s| = |s - s| + 2·|s| - 1`.

Equivalently `2·|s+s| = |s-s| + 2|s| - 1`: the doubled sum-kernel support equals
the difference-kernel support plus `2|s| - 1`.  Both support sizes are
`Θ(|s|²)`, but the difference kernel is *twice as spread out* per element as the
(unordered) sum kernel, and the deficit is exactly the linear term `2|s| - 1`
coming from the diagonal (`0` for differences, the `|s|` "doubles" `2a` for
sums).

## Main result

* `sidon_sum_diff_law` — for a nonempty Sidon set,
  `2·|s + s| = |s - s| + 2·|s| - 1`.

Auxiliary (self-contained) counts proved en route:

* `sidon_sum_card` — `2·|s + s| = |s|·(|s| + 1)` (the sum kernel support).
* `sidon_diff_card` — `|s - s| + |s| = |s|² + 1` (the difference kernel support).

## Tags
Sidon set, B₂ set, sumset, difference set, convolution kernel, conservation law

-- !-- Lab Notes -- !--
**Hypothesis (Hypothesizer).**  Given the exact sum-kernel support
`2|s+s| = |s|(|s|+1)` and the difference-kernel support `|s-s| = |s|²-|s|+1`,
we conjectured a *single* closed identity linking the two kernels with no leftover
error term.  Eliminating `|s|²` between the two counts predicts
`2|s+s| = |s-s| + 2|s| - 1`.

**Experiment (Experimenter).**  On `{1,2,4,8}` (|s|=4): `2·|s+s| = 2·10 = 20`
and `|s-s| + 2|s| - 1 = 13 + 8 - 1 = 20` ✓.  On `{1,2,4,8,16}` (|s|=5, still
Sidon): `2·15 = 30 = 21 + 10 - 1` ✓.  The identity held on every Sidon sample.

**Analysis (Analyst).**  The sum count is proved by the "ordered pair with
`a ≤ b`" injection: `p ↦ a+b` is injective on `{(a,b) : a ≤ b}` and surjects onto
`s+s`, and the cardinality of that half-square is `(|s|²+|s|)/2` via a
swap-involution inclusion–exclusion (`card_union_add_card_inter`).  The
difference count reuses the off-diagonal injection.  Combining the two is then a
purely arithmetic elimination (`omega`) once `|s|·(|s|+1)` is expanded by `ring`.

**Critique (Critic).**  The law is not a definitional triviality: both support
counts genuinely require the Sidon hypothesis — for the non-Sidon `{1,2,3,4}`
one has `|s-s| = 7 ≠ 13 = |s|²-|s|+1` and `2|s+s| = 14 ≠ 20 = |s|(|s|+1)`, so the
individual kernel counts break, and the proof uses injectivity-from-Sidon plus
`omega` arithmetic, never `decide`/`native_decide`.  Nonemptiness is load-bearing
for the `-1` (the empty set gives `0 ≠ 0 + 0 - 1`).

**Synthesis (PI).**  The two convolution kernels obey an exact linear
conservation law; the `2:1` ratio of their supports is the rigorous shadow of the
"L² energy distributed across kernels" heuristic.
-- !-- Lab Notes -- !--
-/

open Finset
open scoped Pointwise

open Catalog.Novelty.SidonMultiKernel.MultiKernelLaw




/-! ### The difference kernel support -/





/-! ### The sum kernel support -/





/-! ### The conservation law -/



open Catalog.Novelty.SidonMultiKernel.MultiKernelLaw in
theorem solution(s : Finset ℤ) :
    2 * ((s ×ˢ s).filter (fun p => p.1 ≤ p.2)).card = s.card * s.card + s.card := by
  set L := (s ×ˢ s).filter (fun p : ℤ × ℤ => p.1 ≤ p.2) with hL
  set L' := (s ×ˢ s).filter (fun p : ℤ × ℤ => p.2 ≤ p.1) with hL'
  have hunion : L ∪ L' = s ×ˢ s := by
    ext p; simp only [hL, hL', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h; rcases le_total p.1 p.2 with hle | hle
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, hle⟩
  have hinter : L ∩ L' = (s ×ˢ s).filter (fun p : ℤ × ℤ => p.1 = p.2) := by
    ext p; simp only [hL, hL', Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h, h1⟩, ⟨_, h2⟩⟩; exact ⟨h, le_antisymm h1 h2⟩
    · rintro ⟨h, he⟩; exact ⟨⟨h, he.le⟩, ⟨h, he.ge⟩⟩
  have hswap : L'.card = L.card := by
    apply Finset.card_bij (fun p _ => (p.2, p.1))
    · rintro ⟨a, b⟩ hp; simp only [hL', hL, Finset.mem_filter, Finset.mem_product] at *
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h; simp only [Prod.mk.injEq] at h; ext <;> simp [h.1, h.2]
    · rintro ⟨a, b⟩ hp; refine ⟨(b, a), ?_, rfl⟩
      simp only [hL, hL', Finset.mem_filter, Finset.mem_product] at *
      exact ⟨⟨hp.1.2, hp.1.1⟩, hp.2⟩
  have hdiag : ((s ×ˢ s).filter (fun p : ℤ × ℤ => p.1 = p.2)).card = s.card := by
    apply Finset.card_bij (fun p _ => p.1)
    · rintro ⟨a, b⟩ hp; simp only [Finset.mem_filter, Finset.mem_product] at hp; exact hp.1.1
    · rintro ⟨a, b⟩ hp ⟨c, d⟩ hq h
      simp only [Finset.mem_filter, Finset.mem_product] at hp hq
      simp only at h; ext
      · exact h
      · rw [← hp.2, ← hq.2, h]
    · intro a ha; refine ⟨(a, a), ?_, rfl⟩; simp [ha]
  have key := Finset.card_union_add_card_inter L L'
  rw [hunion, hinter, hdiag, hswap, Finset.card_product] at key
  omega
