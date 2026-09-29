-- Prove2me | solution 1 for GenTuranK3t.genTuran_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:44:53.427371+00:00
-- url     : https://prove2.me/submissions/7753a6c7-7c47-46f5-aebe-ade0de1ca5ec

-- Sol generated from Bridges/GenTuranAsymptoticBridge.lean
import Mathlib
import Definitions.Def_Bridges_GenTuranAsymptoticBridge
import Theorems.Thm_GenTuranK3t_K3tFree_iff_CNbound
import Theorems.Thm_GenTuranK3t_KabCopies_card_le
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














/-- **Cubic upper bound for `K_{3,t}`-free graphs at the necessary threshold.**
If `G` is `K_{3,t}`-free with `t ≥ b + 1`, then the number of copies of `K_{a,b}` is `O(n^3)`. -/
theorem KabCopies_cubic_of_K3tFree (G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (hbt : b + 1 ≤ t) (hfree : K3tFree G t) :
    (KabCopies G a b).card
      ≤ ((t - 1).choose b * (t - 1).choose (a - 3)) * (Fintype.card V) ^ 3 := by
  have hcn : CNbound G t := (K3tFree_iff_CNbound G (by omega)).1 hfree
  calc (KabCopies G a b).card
      ≤ (Fintype.card V).choose 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) :=
        KabCopies_card_le G ha hb hcn
    _ ≤ (Fintype.card V) ^ 3 * ((t - 1).choose b * (t - 1).choose (a - 3)) := by
        apply Nat.mul_le_mul_right; exact Nat.choose_le_pow (Fintype.card V) 3
    _ = ((t - 1).choose b * (t - 1).choose (a - 3)) * (Fintype.card V) ^ 3 := by ring

/-! ## The bridge to asymptotic analysis

We now carry the combinatorial cubic bound into the language of Landau `O`-notation and limits,
for arbitrary sequences of `K_{3,b+1}`-free graphs. -/

open Filter Asymptotics




open GenTuranK3t in
theorem solution{a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (G : ∀ n, SimpleGraph (Fin n)) [hG : ∀ n, DecidableRel (G n).Adj]
    (hfree : ∀ n, K3tFree (G n) (b + 1)) :
    Tendsto (fun n : ℕ => ((KabCopies (G n) a b).card : ℝ) / (n : ℝ) ^ (a + b))
      atTop (nhds 0) := by
  -- By the combinatorial bound, we have that $(KabCopies (G n) a b).card \leq C \cdot n^3$ for some constant $C$.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ n, ((KabCopies (G n) a b).card : ℝ) ≤ C * (n : ℝ) ^ 3 := by
    use ( b.choose ( a - 3 ) : ℝ );
    intro n;
    convert KabCopies_cubic_of_K3tFree ( G n ) ha hb ( Nat.le_refl ( b + 1 ) ) ( hfree n ) using 1 ; norm_cast ; simp +decide [ mul_comm ];
  refine' squeeze_zero_norm' _ _;
  use fun n => C * ( n : ℝ ) ^ 3 / ( n : ℝ ) ^ ( a + b );
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; aesop;
  · -- Simplify the expression inside the limit.
    suffices h_simp : Filter.Tendsto (fun n : ℕ => C / (n : ℝ) ^ (a + b - 3)) Filter.atTop (nhds 0) by
      refine h_simp.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn; rw [ show ( n : ℝ ) ^ ( a + b ) = ( n : ℝ ) ^ ( a + b - 3 ) * ( n : ℝ ) ^ 3 by rw [ ← pow_add, Nat.sub_add_cancel ( by linarith ) ] ] ; rw [ mul_div_mul_right _ _ ( by positivity ) ] );
    exact tendsto_const_nhds.div_atTop ( Filter.tendsto_pow_atTop ( Nat.sub_ne_zero_of_lt ( by linarith ) ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop )
