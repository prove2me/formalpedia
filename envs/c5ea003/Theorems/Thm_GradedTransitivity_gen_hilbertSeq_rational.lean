-- Prove2me | Theorems.Thm_GradedTransitivity_gen_hilbertSeq_rational
-- name    : GradedTransitivity.gen_hilbertSeq_rational
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:39:18.675984+00:00
-- url     : https://prove2.me/theorems/c6d764c6-941b-4290-928f-5f7db2420609
-- title:
--   Main theorem.
-- statement:
--   **Main theorem.**  If the grades of a graded `G`-set are eventually
--   `r`-transitive, the Hilbert series `â_n t_r(Y_n) qâ¿` is a rational function
--   whose denominator divides `(1-q)^{r+1}`: indeed already `(1-q)` clears it.
--
--   ```lean
--   theorem GradedTransitivity.gen_hilbertSeq_rational(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r) :
--       ∃ P : ℚ[X], (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ) := by sorry
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GradedTransitivity/GSet.lean#L106

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

theorem GradedTransitivity.gen_hilbertSeq_rational(r N : ℕ) (h : ∀ n ≥ N, IsRTransitive (G n) (Y n) r) :
    ∃ P : ℚ[X], (1 - PowerSeries.X) * gen (hilbertSeq G Y r) = (P : PowerSeries ℚ) := by sorry
