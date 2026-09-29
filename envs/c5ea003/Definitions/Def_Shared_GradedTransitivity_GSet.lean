-- Prove2me | Definitions.Def_Shared_GradedTransitivity_GSet
-- name    : Shared_GradedTransitivity_GSet
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:52:43.28719+00:00
-- url     : https://prove2.me/theorems/00622d7b-17bd-4875-82d3-8d5ebf2c6897
-- title:
--   Aether Catalog definitions — Shared_GradedTransitivity_GSet
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.GradedTransitivity.GSet`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/GradedTransitivity/GSet.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_BinomialGF

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

namespace GradedTransitivity

open Polynomial MulAction

/-- The number `t_r(Y)` of `G`-orbits on the set `Fin r ↪ Y` of injective
`r`-tuples of `Y`. -/
noncomputable def torbits (G : Type*) [Group G] (Y : Type*) [MulAction G Y] (r : ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient G (Fin r ↪ Y))

/-- A `G`-set is `r`-transitive when it carries at least one injective
`r`-tuple and `G` permutes those transitively. -/
def IsRTransitive (G : Type*) [Group G] (Y : Type*) [MulAction G Y] (r : ℕ) : Prop :=
  MulAction.IsMultiplyPretransitive G Y r ∧ Nonempty (Fin r ↪ Y)

section Basic

variable {G : Type*} [Group G] {Y : Type*} [MulAction G Y]




end Basic

/-! ### Rationality of the Hilbert series of a graded `G`-set -/

variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]

/-- The `r`-transitivity Hilbert series `∑_n t_r(Y_n) qⁿ` of a graded
`G`-set. -/
noncomputable def hilbertSeq (G : ℕ → Type*) [∀ n, Group (G n)] (Y : ℕ → Type*)
    [∀ n, MulAction (G n) (Y n)] (r : ℕ) : ℕ → ℚ :=
  fun n => (torbits (G n) (Y n) r : ℚ)





/-! ### The exact Hilbert series in the clean case -/



/-! ### A concrete graded `G`-set: the symmetric groups -/




end GradedTransitivity


