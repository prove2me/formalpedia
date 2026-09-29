-- Prove2me | Theorems.Thm_GradedTransitivity_trivial_family_denominator_sharp
-- name    : GradedTransitivity.trivial_family_denominator_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:40:13.522986+00:00
-- url     : https://prove2.me/theorems/2fae5b75-8470-4298-bef6-5e2247741d5e
-- title:
--   Sharpness in the `G`-set setting.
-- statement:
--   **Sharpness in the `G`-set setting.**  For the trivial-group graded set the
--   denominator `(1-q)^r` does not suffice: the exponent `r+1` in the main theorem
--   cannot be lowered without a transitivity hypothesis.
--
--   ```lean
--   theorem GradedTransitivity.trivial_family_denominator_sharp(r : ℕ) :
--       ¬ ∃ P : ℚ[X], (1 - PowerSeries.X) ^ r *
--           gen (hilbertSeq (fun n => (⊥ : Subgroup (Equiv.Perm (Fin n)))) (fun n => Fin n) r)
--         = (P : PowerSeries ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/Sharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/Sharpness.lean#L99

-- Thm stub generated from Shared/GradedTransitivity/Sharpness.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
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

theorem GradedTransitivity.trivial_family_denominator_sharp(r : ℕ) :
    ¬ ∃ P : ℚ[X], (1 - PowerSeries.X) ^ r *
        gen (hilbertSeq (fun n => (⊥ : Subgroup (Equiv.Perm (Fin n)))) (fun n => Fin n) r)
      = (P : PowerSeries ℚ) := by sorry
