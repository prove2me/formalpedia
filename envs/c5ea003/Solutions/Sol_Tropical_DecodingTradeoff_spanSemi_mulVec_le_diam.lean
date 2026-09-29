-- Prove2me | solution 1 for Tropical.DecodingTradeoff.spanSemi_mulVec_le_diam
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:08.425642+00:00
-- url     : https://prove2.me/submissions/b4eaaf32-2352-4bb1-96b7-dbaebb9d9744

-- Sol generated from Tropical/DecodingTradeoff/Core.lean
import Mathlib
import Definitions.Def_Tropical_DecodingTradeoff_Core
/-
# Tropical Span Contraction: the algebraic endpoint of the decoding trade-off

This file develops the *algebraic* half of a cost / failure-probability trade-off for
min-plus (tropical) decoders on a chain (a trellis).

## Setting

Fix a finite nonempty state space `S`. A *tropical transfer matrix* is a function
`A : S → S → ℝ`, acting on cost-to-go vectors by the min-plus rule

  `(A ⊗ v) a = min_b (A a b + v b)`.

A matrix is **tropically stochastic** (`Stochastic`) when every row has minimum `0`;
this is the min-plus analogue of a row-stochastic matrix and is obtained from an
arbitrary matrix by subtracting row minima, an operation that changes neither the
decoder's decisions nor the argmin structure.

The relevant "distance to a constant" is the **span seminorm**
`spanSemi v = max v - min v`, which is exactly the projective quantity a min-plus
decoder is sensitive to (adding a constant to `v` changes no decision).

## Main results

* `spanSemi_mulVec_le` — min-plus propagation is *nonexpansive* for the span seminorm
  (this needs tropical stochasticity).
* `spanSemi_mulVec_le_diam` — a **Dobrushin/Doeblin-type contraction bound**: one
  min-plus step compresses the span below the matrix *diameter* `diam A`,
  *independently of the input vector*. This holds with no hypothesis on `A` at all.
* `mulVec_mmul` — associativity of the min-plus action (the tropical semiring law).
* `spanSemi_windowApply_le_diam` — **absorption theorem**: after a window of `k`
  transfer steps, the span of the propagated vector is at most `diam (A (i+j))`
  for *any* single index `j < k` inside the window; i.e. it is bounded by the
  running minimum of the diameters over the window.
* `tropicalNoiseFloor` — **sharpness**: a two-state example in which the span is
  *exactly* `d` after every positive number of steps.  Hence min-plus memory loss is
  "one-step absorption to the diameter", **not** geometric decay: purely algebraic
  arguments can never produce a bound decaying in the window length `k`.

The last two results are the structural reason why the exponential-in-window-length
failure bound of `Tropical.DecodingTradeoff.Tradeoff` *must* come from probabilistic
independence rather than from tropical algebra.
-/


open Finset

open Tropical.DecodingTradeoff

variable {S : Type*} [Fintype S] [Nonempty S]

/-! ## §1. Tropical minimum and maximum -/



lemma tmin_le (f : S → ℝ) (s : S) : tmin f ≤ f s := Finset.inf'_le f (mem_univ s)

lemma le_tmax (f : S → ℝ) (s : S) : f s ≤ tmax f := Finset.le_sup' f (mem_univ s)


lemma tmax_le {c : ℝ} {f : S → ℝ} (h : ∀ s, f s ≤ c) : tmax f ≤ c :=
  Finset.sup'_le _ _ fun b _ => h b

lemma exists_tmin (f : S → ℝ) : ∃ s, tmin f = f s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) f
  exact ⟨s, hs⟩






/-! ## §2. Min-plus matrices -/





lemma diam_bound (A : S → S → ℝ) (a a' b : S) : A a b - A a' b ≤ diam A := by
  refine le_trans (le_tmax (fun b => A a b - A a' b) b) ?_
  refine le_trans (le_tmax (fun a' => tmax fun b => A a b - A a' b) a') ?_
  exact le_tmax (fun a => tmax fun a' => tmax fun b => A a b - A a' b) a








/-! ## §2b. The monoid of tropically stochastic matrices

Tropically stochastic matrices are closed under the min-plus product, and the diameter is
*monotone* under composition on both sides: the tropical Dobrushin coefficient of a
product never exceeds the coefficient of either factor.  This is the matrix-level
counterpart of the absorption theorem of §3. -/







/-! ## §2c. Sup-norm nonexpansiveness -/




/-! ## §3. Windows -/







/-! ## §4. Sharpness: the tropical noise floor

The absorption theorem cannot be improved to a bound that decays with the window
length `k`.  We exhibit a two-state chain whose span is *exactly* the diameter `d`
after every positive number of steps. -/












open Tropical.DecodingTradeoff in
theorem solution(A : S → S → ℝ) (v : S → ℝ) :
    spanSemi (mulVec A v) ≤ diam A := by
  obtain ⟨a, ha⟩ := exists_tmin (mulVec A v)
  have key : ∀ a', mulVec A v a' - mulVec A v a ≤ diam A := by
    intro a'
    obtain ⟨b, hb⟩ := exists_tmin (fun b => A a b + v b)
    have h1 : mulVec A v a' ≤ A a' b + v b := tmin_le _ b
    have h2 : mulVec A v a = A a b + v b := hb
    have := diam_bound A a' a b
    simp only [mulVec] at h1 h2 ⊢
    linarith
  have hmax : tmax (mulVec A v) ≤ diam A + mulVec A v a := tmax_le fun s => by linarith [key s]
  simp only [spanSemi, ha]
  linarith
