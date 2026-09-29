-- Prove2me | solution 1 for ForkPinning.kfactor_wall
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:41:19.0412+00:00
-- url     : https://prove2.me/submissions/bb722671-3a5d-43c8-a69a-65e8951ad444

-- Sol generated from Probability/ForkPinningKFactors.lean
import Mathlib
import Definitions.Def_Probability_ForkPinningCore
import Definitions.Def_Probability_ForkPinningKFactors
import Theorems.Thm_ForkPinning_last_factor_wall
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

omit [Nonempty Ω] [DecidableEq Ω] [Nonempty Ω'] [Fintype κ] in
lemma fiber_congr_equiv (e : Ω' ≃ Ω) (X : Ω → κ) (k : κ) :
    fiber (fun w => X (e w)) k = (fiber X k).image e.symm := by
  ext w
  simp only [fiber, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro hw
    exact ⟨e w, by simpa [fiber] using hw, e.symm_apply_apply w⟩
  · rintro ⟨a, ha, rfl⟩
    simpa [fiber] using ha

omit [Nonempty Ω] [DecidableEq Ω] [Nonempty Ω'] [Fintype κ] in
lemma prb_congr_equiv (e : Ω' ≃ Ω) (X : Ω → κ) (k : κ) :
    prb (fun w => X (e w)) k = prb X k := by
  have hcard : Fintype.card Ω' = Fintype.card Ω := Fintype.card_congr e
  rw [prb, prb, fiber_congr_equiv e X k,
    Finset.card_image_of_injective _ e.symm.injective, hcard]

omit [Nonempty Ω] [DecidableEq Ω] [Nonempty Ω'] in
lemma H_congr_equiv (e : Ω' ≃ Ω) (X : Ω → κ) : H (fun w => X (e w)) = H X := by
  simp only [H, prb_congr_equiv e X]

omit [Nonempty Ω] [DecidableEq Ω] [Nonempty Ω'] in
/-- **Mutual information is a relabelling invariant.**  Renaming the sample space by a bijection
changes neither entropy nor mutual information. -/
theorem mutualInfo_congr_equiv (e : Ω' ≃ Ω) (X : Ω → κ) (Y : Ω → β) :
    mutualInfo (fun w => X (e w)) (fun w => Y (e w)) = mutualInfo X Y := by
  have hjoint : joint (fun w => X (e w)) (fun w => Y (e w)) = fun w => (joint X Y) (e w) := rfl
  rw [mutualInfo, mutualInfo, H_congr_equiv e X, H_congr_equiv e Y, hjoint,
    H_congr_equiv e (joint X Y)]


/-! ## The wall in its general form -/


variable {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]






/-! ## `k`-fold products -/


variable {G : Type*} [Group G] [Fintype G] [Nonempty G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]


omit [Fintype G] [Nonempty G] [DecidableEq G] in
/-- Appending a factor at the end multiplies the product on the right. -/
lemma vecProd_snoc {k : ℕ} (u : Fin k → G) (g : G) :
    vecProd (Fin.snoc u g) = vecProd u * g := by
  rw [vecProd, vecProd, List.ofFn_succ']
  simp [List.concat_eq_append, Fin.snoc_castSucc, Fin.snoc_last]







open ForkPinning in
theorem solution{k : ℕ} (F : (Fin k → G) → β) :
    mutualInfo (fun v : Fin (k + 1) → G => vecProd v)
      (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc)) = 0 := by
  have hEq : mutualInfo (fun p : (Fin k → G) × G => vecProd ((snocEquiv k G) p))
      (fun p : (Fin k → G) × G => F (fun i => ((snocEquiv k G) p) i.castSucc))
      = mutualInfo (fun v : Fin (k + 1) → G => vecProd v)
        (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc)) :=
    mutualInfo_congr_equiv (snocEquiv k G) (fun v : Fin (k + 1) → G => vecProd v)
      (fun v : Fin (k + 1) → G => F (fun i => v i.castSucc))
  rw [← hEq]
  have h1 : (fun p : (Fin k → G) × G => vecProd ((snocEquiv k G) p))
      = fun p : (Fin k → G) × G => vecProd p.1 * p.2 := by
    funext p
    show vecProd (Fin.snoc p.1 p.2) = vecProd p.1 * p.2
    exact vecProd_snoc p.1 p.2
  have h2 : (fun p : (Fin k → G) × G => F (fun i => ((snocEquiv k G) p) i.castSucc))
      = fun p : (Fin k → G) × G => F p.1 := by
    funext p
    show F (fun i => Fin.snoc (α := fun _ => G) p.1 p.2 i.castSucc) = F p.1
    congr 1
    funext i
    simp
  rw [h1, h2]
  exact last_factor_wall (fun u : Fin k → G => vecProd u) F
