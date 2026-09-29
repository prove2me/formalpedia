-- Prove2me | solution 1 for GradedTransitivity.torbits_of_trivial_action
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:54:31.089902+00:00
-- url     : https://prove2.me/submissions/6607d403-d19a-45cd-8f4c-d11dbb6a7d9b

-- Sol generated from Shared/GradedTransitivity/Sharpness.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_Newton

/-!
# Sharpness of the exponent in the `G`-set setting

The main theorem says that *eventual `r`-transitivity* gives denominator
`(1-q)`, hence a fortiori a denominator dividing `(1-q)^{r+1}`.  Is the
exponent `r+1` in the general statement wasteful?  No: as soon as
transitivity is dropped, the exponent `r+1` is attained *and needed*.

We exhibit this with the graded `G`-set `Y_n = Fin n` acted on by the trivial
group `G_n = ⊥ ≤ Perm (Fin n)`.  Here every injective `r`-tuple is its own
orbit, so

`t_r(Y_n) = n(n-1)⋯(n-r+1) = r! · C(n,r)`,

whose generating function is `r!·q^r/(1-q)^{r+1}` — a genuine pole of order
`r+1` at `q = 1`.

## Main results

* `torbits_of_trivial_action` : trivial actions count injective tuples.
* `torbits_bot` : `t_r = n.descFactorial r` for the trivial-group family.
* `trivial_family_generating_function` : the exact Hilbert series.
* `trivial_family_denominator_sharp` : `(1-q)^r` does *not* suffice, so the
  exponent `r+1` of the main theorem is optimal in the absence of
  transitivity.
-/

open GradedTransitivity

open Polynomial

/-! ### Trivial actions -/


/-! ### The trivial-group graded set -/








open GradedTransitivity in
theorem solution{G : Type*} [Group G] {Y : Type*} [MulAction G Y]
    (htriv : ∀ (g : G) (y : Y), g • y = y) (r : ℕ) :
    torbits G Y r = Nat.card (Fin r ↪ Y) := by
  have hfix : ∀ (g : G) (f : Fin r ↪ Y), g • f = f := by
    intro g f
    ext i
    exact htriv g (f i)
  have hwd : ∀ x y : Fin r ↪ Y, (MulAction.orbitRel G (Fin r ↪ Y)) x y → id x = id y := by
    intro x y hxy
    have hmem : x ∈ MulAction.orbit G y := hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hmem
    rw [id, id, ← hg, hfix]
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.lift (s := MulAction.orbitRel G (Fin r ↪ Y)) id hwd) ⟨?_, ?_⟩)
  · intro q q' hq
    induction q using Quotient.inductionOn with
    | h a =>
      induction q' using Quotient.inductionOn with
      | h b =>
        simpa using congrArg (Quotient.mk (MulAction.orbitRel G (Fin r ↪ Y))) hq
  · intro f
    exact ⟨Quotient.mk _ f, rfl⟩
