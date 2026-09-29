-- Prove2me | solution 1 for Tropical.DecodingTradeoff.mulVec_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:31:06.904589+00:00
-- url     : https://prove2.me/submissions/0fc46fc3-4fb3-4920-9bba-47258d252504

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


lemma exists_tmin (f : S → ℝ) : ∃ s, tmin f = f s := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) f
  exact ⟨s, hs⟩






/-! ## §2. Min-plus matrices -/













/-! ## §2b. The monoid of tropically stochastic matrices

Tropically stochastic matrices are closed under the min-plus product, and the diameter is
*monotone* under composition on both sides: the tropical Dobrushin coefficient of a
product never exceeds the coefficient of either factor.  This is the matrix-level
counterpart of the absorption theorem of §3. -/







/-! ## §2c. Sup-norm nonexpansiveness -/

lemma mulVec_mono (A : S → S → ℝ) {v w : S → ℝ} (h : ∀ s, v s ≤ w s) (a : S) :
    mulVec A v a ≤ mulVec A w a :=
  le_tmin fun b => le_trans (tmin_le (fun b => A a b + v b) b) (by linarith [h b])

lemma mulVec_add_const (A : S → S → ℝ) (v : S → ℝ) (c : ℝ) (a : S) :
    mulVec A (fun s => v s + c) a = mulVec A v a + c := by
  refine le_antisymm ?_ ?_
  · obtain ⟨b, hb⟩ := exists_tmin (fun b => A a b + v b)
    have h1 : mulVec A (fun s => v s + c) a ≤ A a b + (v b + c) := tmin_le _ b
    simp only [mulVec] at h1 hb ⊢
    rw [hb]; linarith
  · obtain ⟨b, hb⟩ := exists_tmin (fun b => A a b + (v b + c))
    have h1 : mulVec A v a ≤ A a b + v b := tmin_le _ b
    simp only [mulVec] at h1 hb ⊢
    rw [hb]; linarith


/-! ## §3. Windows -/







/-! ## §4. Sharpness: the tropical noise floor

The absorption theorem cannot be improved to a bound that decays with the window
length `k`.  We exhibit a two-state chain whose span is *exactly* the diameter `d`
after every positive number of steps. -/












open Tropical.DecodingTradeoff in
theorem solution(A : S → S → ℝ) (v w : S → ℝ) (a : S) :
    |mulVec A v a - mulVec A w a| ≤ tmax (fun s => |v s - w s|) := by
  set M := tmax (fun s => |v s - w s|) with hM
  have hvw : ∀ s, v s ≤ w s + M := fun s => by
    have := le_tmax (fun s => |v s - w s|) s
    have h2 : v s - w s ≤ |v s - w s| := le_abs_self _
    rw [← hM] at this; linarith
  have hwv : ∀ s, w s ≤ v s + M := fun s => by
    have := le_tmax (fun s => |v s - w s|) s
    have h2 : w s - v s ≤ |v s - w s| := by
      rw [abs_sub_comm]; exact le_abs_self _
    rw [← hM] at this; linarith
  have h1 : mulVec A v a ≤ mulVec A w a + M := by
    have := mulVec_mono A hvw a
    rwa [mulVec_add_const] at this
  have h2 : mulVec A w a ≤ mulVec A v a + M := by
    have := mulVec_mono A hwv a
    rwa [mulVec_add_const] at this
  rw [abs_le]
  constructor <;> linarith
