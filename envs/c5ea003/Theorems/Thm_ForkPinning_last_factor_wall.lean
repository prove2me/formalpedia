-- Prove2me | Theorems.Thm_ForkPinning_last_factor_wall
-- name    : ForkPinning.last_factor_wall
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:36:05.553575+00:00
-- url     : https://prove2.me/theorems/59287996-77bf-4aa7-a0ce-9e8f70f3f9f3
-- title:
--   The which-factor wall, general form.
-- statement:
--   **The which-factor wall, general form.**  For a uniformly random pair `(u, v)` in `Ω × G`,
--   the "class of the product" `h(u)·v` is exactly independent of *every* statistic `F(u)` of the
--   remaining data: the free last factor destroys all information.
--
--   ```lean
--   theorem ForkPinning.last_factor_wall(h : Ω → G) (F : Ω → β) :
--       mutualInfo (fun x : Ω × G => h x.1 * x.2) (fun x : Ω × G => F x.1) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForkPinningKFactors.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForkPinningKFactors.lean#L123

-- Thm stub generated from Probability/ForkPinningKFactors.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningKFactors
/-
# The which-factor wall for a product of `k` primes

`ForkPinningSemiprimeGeneral` proves that for a semiprime `N = p q` the class of `N` in a finite
group `G` is *exactly* independent of every statistic of the first factor.  This file closes the
"wall" half of conjecture **C7** of `FUTURE_DIRECTIONS.md`: the same is true for a product of
arbitrarily many primes, and in the strongest possible form.

The key structural fact is that the class map is a group homomorphism with *uniform fibres in the
last coordinate*: whatever the classes of the first `k` primes are, the class of the last one is
free, so the class of the product is uniform **conditionally on everything else**.  We isolate
this as `ForkPinning.last_factor_wall`, which is stated for an arbitrary aggregate
`h : Ω → G` of the other factors, and then instantiate it at `Ω = Fin k → G`.

Main results:

* `ForkPinning.mutualInfo_congr_equiv` : mutual information is invariant under a relabelling of
  the sample space (a reusable transport lemma).
* `ForkPinning.prb_lastMul_uniform` : the class of the product is exactly uniform.
* `ForkPinning.last_factor_wall` : `I( h(u)·v ; F(u) ) = 0` for every aggregate `h` and every
  statistic `F` of the remaining data — the wall in its general form.
* `ForkPinning.kfactor_wall` : for `N = p₁ ⋯ p_{k+1}` with independent uniform classes, the class
  of `N` carries **exactly zero** information about any statistic of `p₁, …, p_k`.
* `ForkPinning.kfactor_wall_which_splits` : in particular it says nothing about *which* of the
  first `k` primes split, and `kfactor_class_uniform` : the class of `N` is uniform, so it says
  nothing at all in isolation either.
-/


open ForkPinning

open Finset Real

/-! ## Transport of the information functionals along a relabelling of the sample space -/


variable {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable [Fintype Ω'] [Nonempty Ω'] [DecidableEq Ω']
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]






/-! ## The wall in its general form -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]

theorem ForkPinning.last_factor_wall(h : Ω → G) (F : Ω → β) :
    mutualInfo (fun x : Ω × G => h x.1 * x.2) (fun x : Ω × G => F x.1) = 0 := by sorry
