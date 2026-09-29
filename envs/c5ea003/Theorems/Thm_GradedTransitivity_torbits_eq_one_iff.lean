-- Prove2me | Theorems.Thm_GradedTransitivity_torbits_eq_one_iff
-- name    : GradedTransitivity.torbits_eq_one_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:07.997419+00:00
-- url     : https://prove2.me/theorems/78c65f11-80e5-40ae-9d19-95165d33c62d
-- title:
--   `r`-transitivity is exactly the statement `t_r(Y) = 1`.
-- statement:
--   `r`-transitivity is exactly the statement `t_r(Y) = 1`.
--
--   ```lean
--   theorem GradedTransitivity.torbits_eq_one_iff(r : ℕ) : torbits G Y r = 1 ↔ IsRTransitive G Y r := by sorry
--
--
--   /-! ### Rationality of the Hilbert series of a graded `G`-set -/
--
--   variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]
--
--
--
--
--
--
--   /-! ### The exact Hilbert series in the clean case -/
--
--
--
--   /-! ### A concrete graded `G`-set: the symmetric groups -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GradedTransitivity/GSet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/GSet.lean#L62

-- Thm stub generated from Shared/GradedTransitivity/GSet.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF
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

theorem GradedTransitivity.torbits_eq_one_iff(r : ℕ) : torbits G Y r = 1 ↔ IsRTransitive G Y r := by sorry
