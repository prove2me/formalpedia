-- Prove2me | Definitions.Def_Probability_ForkPinningKFactors
-- name    : Probability_ForkPinningKFactors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:16.168704+00:00
-- url     : https://prove2.me/theorems/808c7469-3190-4ba2-ab03-85387fb6d404
-- title:
--   Aether Catalog definitions — Probability_ForkPinningKFactors
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForkPinningKFactors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForkPinningKFactors.lean by skeleton subtraction
import Mathlib
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


namespace ForkPinning

open Finset Real

/-! ## Transport of the information functionals along a relabelling of the sample space -/

section Transport

variable {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable [Fintype Ω'] [Nonempty Ω'] [DecidableEq Ω']
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]





end Transport

/-! ## The wall in its general form -/

section Wall

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]





end Wall

/-! ## `k`-fold products -/

section KFactors

variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-- The product of a vector of group elements, taken in index order. -/
def vecProd {H : Type*} [Group H] {k : ℕ} (v : Fin k → H) : H := (List.ofFn v).prod


/-- Splitting off the last coordinate of a vector of classes. -/
def snocEquiv (k : ℕ) (G : Type*) : (Fin k → G) × G ≃ (Fin (k + 1) → G) where
  toFun p := Fin.snoc p.1 p.2
  invFun v := (fun i => v i.castSucc, v (Fin.last k))
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext i; simp
    · simp
  right_inv v := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp
    · intro j; simp




end KFactors

end ForkPinning


