-- Prove2me | solution 1 for GenTuranK3t.K3tFree_iff_CNbound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:41:58.845253+00:00
-- url     : https://prove2.me/submissions/13d863b1-1429-44bd-9fe4-ea047802cd48

-- Sol generated from Bridges/GenTuranAsymptoticBridge.lean
import Mathlib
import Definitions.Def_Bridges_GenTuranAsymptoticBridge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: Generalized Turán counting (extremal combinatorics) ↔ Landau asymptotics (analysis)

The generalized Turán problem asks for the maximum number of copies of a fixed graph `H`
inside an `n`-vertex host graph that avoids a forbidden subgraph `F`.  For `H = K_{a,b}` and
`F = K_{3,b+1}` (with `3 ≤ a ≤ b`) the maximum is `Θ(n^3)`; the *upper* half of this statement
is a Kővári–Sós–Turán-style double count, reproduced here self-containedly as
`KabCopies_cubic_of_K3tFree`.

This file is a **connector**: it re-expresses that purely combinatorial cardinality bound as a
statement in the language of *asymptotic analysis*, using Mathlib's `Asymptotics.IsBigO` and
`Filter.Tendsto`.  Concretely, for any sequence `G : ∀ n, SimpleGraph (Fin n)` of
`K_{3,b+1}`-free graphs:

* `genTuran_KabCopies_isBigO` : the count `n ↦ #{copies of K_{a,b} in Gₙ}` is `O(n^3)` in the
  Landau sense (`=O[atTop]`).  The Landau constant is the *combinatorial* constant
  `C(b, a-3)` — the bridge carries the extremal constant into the analytic statement.
* `genTuran_density_tendsto_zero` : the normalized "copy density" `#copies / n^{a+b}` tends to
  `0`.  Since a labelled `K_{a,b}` lives on `a+b ≥ 6` vertices while the count is only cubic,
  the fraction of vertex placements realizing a copy vanishes — a probabilistic/analytic
  reading of the same extremal fact.

The two named results genuinely *consume* the combinatorial theorem `KabCopies_cubic_of_K3tFree`
as a black box, so the file is a faithful bridge rather than a restatement.

## Catalog connections
* `Generalized Turán number` / `Alon–Shikhelman`: `KabCopies` is the counting object.
* `Kővári–Sós–Turán theorem`: `cnbhd_card_le` is the common-neighborhood cap that drives the
  double count.
* `Complete bipartite graphs`: both the counted graph `K_{a,b}` and the forbidden `K_{3,b+1}`.
-/

open Finset

open GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The combinatorial core (self-contained upper bound)

The material in this section reproduces the elementary `O(n^3)` upper bound for
`ex(n, K_{a,b}, K_{3,t})`, so that the asymptotic bridge below is self-contained. -/


@[simp] lemma mem_cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (w : V) :
    w ∈ cnbhd G S ↔ ∀ u ∈ S, G.Adj u w := by
  simp [cnbhd]













/-! ## The bridge to asymptotic analysis

We now carry the combinatorial cubic bound into the language of Landau `O`-notation and limits,
for arbitrary sequences of `K_{3,b+1}`-free graphs. -/

open Filter Asymptotics




open GenTuranK3t in
theorem solution(G : SimpleGraph V) [DecidableRel G.Adj] {t : ℕ} (ht : 1 ≤ t) :
    K3tFree G t ↔ CNbound G t := by
  constructor
  · intro hfree S hS
    by_contra hcon
    push_neg at hcon
    have ht' : t ≤ (cnbhd G S).card := by omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq ht'
    refine hfree ⟨S, B, hS, hBcard, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro a haS haB
      exact G.irrefl ((mem_cnbhd G S a).1 (hBsub haB) a haS)
    · intro u hu v hv
      exact (mem_cnbhd G S v).1 (hBsub hv) u hu
  · intro hcn ⟨A, B, hA, hB, _hdisj, hcomp⟩
    have hBsub : B ⊆ cnbhd G A := by
      intro v hv; rw [mem_cnbhd]; intro u hu; exact hcomp u hu v hv
    have h1 : t ≤ (cnbhd G A).card := by rw [← hB]; exact card_le_card hBsub
    have h2 := hcn A hA
    omega
