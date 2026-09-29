-- Prove2me | solution 1 for GradedTransitivity.torbits_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:47:50.485854+00:00
-- url     : https://prove2.me/submissions/afbce6d3-b3b1-4fb6-a8a7-347dad2a48f5

-- Sol generated from Shared/GradedTransitivity/GSet.lean
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

/-- The orbit space of a pretransitive action is a subsingleton. -/
theorem subsingleton_orbitQuotient {α : Type*} [MulAction G α] [IsPretransitive G α] :
    Subsingleton (MulAction.orbitRel.Quotient G α) := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | h a =>
    induction y using Quotient.inductionOn with
    | h b =>
      have hab : a ∈ MulAction.orbit G b :=
        MulAction.mem_orbit_iff.2 (MulAction.exists_smul_eq G b a)
      exact Quotient.sound hab




/-! ### Rationality of the Hilbert series of a graded `G`-set -/







/-! ### The exact Hilbert series in the clean case -/



/-! ### A concrete graded `G`-set: the symmetric groups -/





open GradedTransitivity in
theorem solution(r : ℕ) : torbits G Y r = 1 ↔ IsRTransitive G Y r := by
  constructor
  · intro h
    obtain ⟨hsub, hne⟩ := Nat.card_eq_one_iff_unique.1 h
    have hY : Nonempty (Fin r ↪ Y) := by
      obtain ⟨q⟩ := hne
      induction q using Quotient.inductionOn with
      | h a => exact ⟨a⟩
    refine ⟨⟨fun x y => ?_⟩, hY⟩
    have : (Quotient.mk (MulAction.orbitRel G (Fin r ↪ Y)) x)
        = Quotient.mk (MulAction.orbitRel G (Fin r ↪ Y)) y := Subsingleton.elim _ _
    have hmem : x ∈ MulAction.orbit G y := Quotient.exact this
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hmem
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  · rintro ⟨htr, hne⟩
    have : IsPretransitive G (Fin r ↪ Y) := htr
    have hsub : Subsingleton (MulAction.orbitRel.Quotient G (Fin r ↪ Y)) :=
      subsingleton_orbitQuotient
    have hnq : Nonempty (MulAction.orbitRel.Quotient G (Fin r ↪ Y)) :=
      ⟨Quotient.mk _ hne.some⟩
    exact Nat.card_eq_one_iff_unique.2 ⟨hsub, hnq⟩
