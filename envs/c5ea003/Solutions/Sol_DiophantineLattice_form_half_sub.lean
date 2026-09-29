-- Prove2me | solution 1 for DiophantineLattice.form_half_sub
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T12:33:36.961927+00:00
-- url     : https://prove2.me/submissions/fb028c07-d76d-4ab3-b17d-f40732706ae6

/-
# `DiophantineLattice.form_half_sub`
Target `bcf0065d` (Open; re-read live before submitting).

ORDINARY PROOF — bundle recovered from the graph, Theorems screen CLEAN. Gift: checked at ship time.

BINDERS — no WA exists (CE x5). The bundle has a SINGLE `variable {n : ℕ}` at line 60 with no
staging, so the statement's own binders are complete.

DEFINITIONS (read from source):
    bil B x y  = ∑ i, ∑ j, B i j * x i * y j
    form B x   = bil B x x
    emb m i    = (m i : ℚ)
    halfPt v i = (v i : ℚ) / 2

MATHS. `halfPt v i - emb m i = v i / 2 - m i = (v i - 2 * m i) / 2`, exactly HALF the right-hand
argument `emb (v - 2m) i`. `form` is homogeneous of degree 2, so halving the argument quarters the
form. Pull `/4` out through both sums and clear the integer casts termwise.
-/
import Mathlib
import Definitions.Def_Novelty_DiophantineLatticeSpectralGap

set_option autoImplicit false
set_option maxHeartbeats 400000

open DiophantineLattice Finset

open DiophantineLattice in
/-- **The target, verbatim.** -/
theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (v m : Fin n → ℤ) :
    form B (fun i => halfPt v i - emb m i)
      = form B (emb (fun i => v i - 2 * m i)) / 4 := by
  simp only [form, bil, halfPt, emb]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast
  ring
