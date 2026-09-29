-- Prove2me | Theorems.Thm_GradedTransitivity_perm_graded_gen
-- name    : GradedTransitivity.perm_graded_gen
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:24.656243+00:00
-- url     : https://prove2.me/theorems/aac1a03e-7794-4742-b976-08024cf82346
-- title:
--   The symmetric-group graded set realises `q^r/(1-q)`.
-- statement:
--   **The symmetric-group graded set realises `q^r/(1-q)`.**  For
--   `Y_n = Fin n` with `G_n = Equiv.Perm (Fin n)` one has
--   `â_n t_r(Y_n) qâ¿ = q^r/(1-q)`; in particular the denominator is the divisor
--   `1-q` of `(1-q)^{r+1}`, and the numerator is `q^r`.
--
--   ```lean
--   theorem GradedTransitivity.perm_graded_gen(r : ℕ) :
--       (1 - PowerSeries.X) *
--           gen (hilbertSeq (fun n => Equiv.Perm (Fin n)) (fun n => Fin n) r)
--         = (PowerSeries.X : PowerSeries ℚ) ^ r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/GSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/GSet.lean#L214

-- Thm stub generated from Shared/GradedTransitivity/GSet.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet

/-!
# Graded `G`-sets, `r`-transitivity, and rational Hilbert series

Let `Y = ⨆_n Y_n` be a graded `G`-set (a family of `G`-sets indexed by the
grade `n`).  Following Mathlib's `MulAction.IsMultiplyPretransitive`, the
`r`-tuple object of a `G`-set `Y` is the `G`-set `Fin r ↪ Y` of injective
`r`-tuples, and we write

`t_r(Y) = #(orbits of G on Fin r ↪ Y)`.

The grade `Y_n` is *`r`-transitive* when `G` acts transitively on the nonempty
set `Fin r ↪ Y_n`, which is exactly `t_r(Y_n) = 1`.

## Main results

* `torbits_eq_one_iff` : `t_r(Y) = 1` iff `Y` is `r`-transitive.
* `gen_torbits_rational` : if `Y_n` is `r`-transitive for all large `n` then
  `∑_n t_r(Y_n) qⁿ` is `P(q)/(1-q)^{r+1}` with `P` a polynomial; moreover
  the denominator can be taken to be the divisor `1-q` of `(1-q)^{r+1}`.
* `gen_torbits_eq_of_exactly` : the exact Hilbert series `q^N/(1-q)` in the
  clean case where the grades below `N` carry no injective `r`-tuple.
* `perm_graded_gen` : the symmetric-group family `Y_n = Fin n`,
  `G_n = Equiv.Perm (Fin n)` realises `∑_n t_r(Y_n) qⁿ = q^r/(1-q)`.

The companion file `BinomialGF` shows that the exponent `r+1` is optimal for
general polynomial growth, so the theorem here is a genuine strengthening in
the transitive regime: eventual `r`-transitivity forces denominator `1-q`.
-/

open GradedTransitivity

open Polynomial MulAction




variable {G : Type*} [Group G] {Y : Type*} [MulAction G Y]





/-! ### Rationality of the Hilbert series of a graded `G`-set -/

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]






/-! ### The exact Hilbert series in the clean case -/



/-! ### A concrete graded `G`-set: the symmetric groups -/

theorem GradedTransitivity.perm_graded_gen(r : ℕ) :
    (1 - PowerSeries.X) *
        gen (hilbertSeq (fun n => Equiv.Perm (Fin n)) (fun n => Fin n) r)
      = (PowerSeries.X : PowerSeries ℚ) ^ r := by sorry
