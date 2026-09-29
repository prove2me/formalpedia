-- Prove2me | solution 1 for Logic.PhaseRoute.cov_fst_snd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T11:32:35.372976+00:00
-- url     : https://prove2.me/submissions/3bc08dab-b499-414b-9bc2-e9ee5403693e

/-
# `Logic.PhaseRoute.cov_fst_snd_eq_zero`
Target `76bab845` (Open; re-read live immediately before submitting).

ORDINARY PROOF — bundle built, closure screens CLEAN. Gift: **SAFE**.

BINDERS — expected type from this target's OWN WA, verbatim (it carries THREE):
    ∀ {α β} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β] (f : α → ℝ) (g : β → ℝ),
      (cov (fun x => f x.1) fun x => g x.2) = 0

DEFINITIONS (read from source, LeastSquares:41/44):
    avg (f : ι → ℝ)  = (∑ i, f i) / (Fintype.card ι : ℝ)
    cov (f g : ι → ℝ) = avg (fun i => f i * g i) - avg f * avg g

MATHS — distinct blocks are uncorrelated. Writing `F x = f x.1` and `G x = g x.2`:
  * `avg (F·G)` : the product sum FACTORS, `∑_{(a,b)} f a · g b = (∑ f)·(∑ g)`, so dividing by
    `|α|·|β|` gives `(∑f/|α|)·(∑g/|β|) = avg f · avg g`;
  * `avg F = avg f` and `avg G = avg g` are the two projection lemmas.
So `cov = avg f · avg g − avg f · avg g = 0`. The factorisation IS the independence: nothing about
`f` or `g` is used beyond their depending on different coordinates.

The three lemmas this rests on are separate targets in this bundle, so all are RE-DERIVED INLINE —
importing from `Theorems/` would force the reduction path and an axiom audit.

PROBED, NOT GUESSED — all `#check`ed, and the factorisation step compiled outright in the probe:
  * `Finset.sum_mul_sum (s t f g) : (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j`
  * `Fintype.sum_prod_type`, `Finset.sum_const`, `Fintype.card_prod`
-/
import Mathlib
import Definitions.Def_Logic_PhaseRouteAlignment

set_option autoImplicit false
set_option maxHeartbeats 400000

open Logic.PhaseRoute Finset

open Logic.PhaseRoute in
/-- **The target, verbatim.** -/
theorem solution {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (f : α → ℝ) (g : β → ℝ) :
    cov (fun x : α × β => f x.1) (fun x : α × β => g x.2) = 0 := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    positivity
  have hβ : (Fintype.card β : ℝ) ≠ 0 := by
    have h : 0 < Fintype.card β := Fintype.card_pos
    positivity
  -- the product sum FACTORS -- this is the independence
  have hprod : (∑ x : α × β, f x.1 * g x.2) = (∑ a, f a) * ∑ b, g b := by
    rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hf : (∑ x : α × β, f x.1) = (Fintype.card β : ℝ) * ∑ a, f a := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, Finset.sum_mul, mul_comm]
  have hg : (∑ x : α × β, g x.2) = (Fintype.card α : ℝ) * ∑ b, g b := by
    rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ]
  rw [cov, avg, avg, avg, hprod, hf, hg, Fintype.card_prod, Nat.cast_mul]
  field_simp
  ring
