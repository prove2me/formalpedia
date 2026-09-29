-- Prove2me | solution 1 for Tropical.DecodingTradeoff.spanSemi_add_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:07.885987+00:00
-- url     : https://prove2.me/submissions/50b1f84e-8039-4ec5-8f96-d341309d7612

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

lemma le_tmin {c : ℝ} {f : S → ℝ} (h : ∀ s, c ≤ f s) : c ≤ tmin f :=
  Finset.le_inf' _ _ fun b _ => h b

lemma tmax_le {c : ℝ} {f : S → ℝ} (h : ∀ s, f s ≤ c) : tmax f ≤ c :=
  Finset.sup'_le _ _ fun b _ => h b

lemma exists_tmin (f : S → ℝ) : ∃ s, tmin f = f s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) f
  exact ⟨s, hs⟩

lemma exists_tmax (f : S → ℝ) : ∃ s, tmax f = f s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := S)) f
  exact ⟨s, hs⟩





/-! ## §2. Min-plus matrices -/













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
theorem solution(v : S → ℝ) (c : ℝ) : spanSemi (fun s => v s + c) = spanSemi v := by
  have h1 : tmax (fun s => v s + c) = tmax v + c := by
    refine le_antisymm (tmax_le fun s => by linarith [le_tmax v s]) ?_
    obtain ⟨s, hs⟩ := exists_tmax v
    have := le_tmax (fun s => v s + c) s
    rw [hs]; linarith
  have h2 : tmin (fun s => v s + c) = tmin v + c := by
    refine le_antisymm ?_ (le_tmin fun s => by linarith [tmin_le v s])
    obtain ⟨s, hs⟩ := exists_tmin v
    have := tmin_le (fun s => v s + c) s
    rw [hs]; linarith
  simp only [spanSemi, h1, h2]; ring
