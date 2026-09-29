-- Prove2me | Theorems.Thm_GradedTransitivity_torbits_of_trivial_action
-- name    : GradedTransitivity.torbits_of_trivial_action
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:40:06.684987+00:00
-- url     : https://prove2.me/theorems/964211bf-6f7b-42d9-8268-075e208e502a
-- title:
--   If `G` acts trivially on `Y`, then `t_r(Y)` is just the number of injective
-- statement:
--   If `G` acts trivially on `Y`, then `t_r(Y)` is just the number of injective
--   `r`-tuples of `Y`.
--
--   ```lean
--   theorem GradedTransitivity.torbits_of_trivial_action{G : Type*} [Group G] {Y : Type*} [MulAction G Y]
--       (htriv : ∀ (g : G) (y : Y), g • y = y) (r : ℕ) :
--       torbits G Y r = Nat.card (Fin r ↪ Y) := by sorry
--   /-! ### The trivial-group graded set -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Sharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Sharpness.lean#L35

-- Thm stub generated from Shared/GradedTransitivity/Sharpness.lean
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

theorem GradedTransitivity.torbits_of_trivial_action{G : Type*} [Group G] {Y : Type*} [MulAction G Y]
    (htriv : ∀ (g : G) (y : Y), g • y = y) (r : ℕ) :
    torbits G Y r = Nat.card (Fin r ↪ Y) := by sorry
