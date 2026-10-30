-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.ParamClass.begf_involutionsByComponents
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:56.77751+00:00
-- url     : https://prove2.me/submissions/b60d8906-e61e-4f41-8c88-5c78fd907a5a

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_SeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSeqMarked
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSetMarked
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — Fibonacci numbers as compositions into parts `1` and `2`

Flajolet & Sedgewick, Part A, Chapter I, §I.3. Let `D` be the class with one
object of size `1` and one of size `2`. Then `SEQ(D)` enumerates compositions of
`n` into parts of size `1` and `2`, and

* `counts_seq_parts12` — there are `F_{n+1}` of them (`Nat.fib (n+1)`), via the
  convolution recursion `counts_seq_succ`, which here is the Fibonacci recurrence;
* `ogf_parts12` / `ogf_seq_parts12` — `D(z) = z + z²` and the OGF is
  `1/(1 - z - z²)`, the Fibonacci generating function.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_parts12 (n : ℕ) :
    CombClass.parts12.counts n = if n = 1 then 1 else if n = 2 then 1 else 0 :=
  Fintype.card_fin _

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — ODE machinery for the labelled set construction

Toward the labelled set transfer `SET(C)(z) = exp(C(z))` (F&S §II.2). The strategy
(differential route): `exp(C(z))` and `SET(C)(z)` both satisfy the linear ODE
`F' = C'(z)·F` with constant term `1`, and that ODE has a unique solution. This file
proves the two *general* (combinatorics-free) ingredients:

* `subst_exp_ode` — `exp(C(z)) := (exp ℚ).subst C.egf` satisfies `F' = C'·F`
  (the chain rule `derivative_subst` + `derivative_exp`).
* `ode_unique` — a power series with `H' = G·H` and `H(0) = 0` is `0`.

The remaining (combinatorial) ingredient — that `SET(C).egf` satisfies the same ODE,
via a pointing bijection on set partitions — is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- **ODE uniqueness**: a power series solving `H' = G·H` with vanishing constant term
is `0` (coefficient induction). -/
theorem ode_unique {R : Type*} [CommSemiring R] [Algebra ℚ R] {H G : R⟦X⟧}
    (hode : d⁄dX R H = G * H)
    (h0 : constantCoeff H = 0) : H = 0 := by
  have key : ∀ n, coeff n H = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff_apply]; exact h0
      | m + 1 =>
        have hd := congrArg (coeff m) hode
        rw [coeff_derivative, coeff_mul,
          Finset.sum_eq_zero (fun p hp => ?_)] at hd
        · have hu : IsUnit ((m : R) + 1) := by
            simpa using
              (IsUnit.map (algebraMap ℚ R)
                (isUnit_iff_ne_zero.mpr (by positivity : ((m : ℚ) + 1) ≠ 0)))
          exact hu.mul_left_eq_zero.mp hd
        · rw [Finset.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
  ext n
  rw [key n, map_zero]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

lemma prod_parts_sdiffSubtype (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (∏ A : (finpartitionSdiffSubtype B Q).parts, C.counts A.val.card) =
      ∏ A : Q.parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort (finpartitionSdiffSubtype B Q).parts
      (fun A : Finset {x : α // x ∉ B} => C.counts A.card),
    Finset.prod_coe_sort Q.parts (fun A : Finset α => C.counts A.card)]
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : ∀ A ∈ Q.parts, ∀ D ∈ Q.parts,
      A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) → A = D := by
    intro A hA D hD hsub
    ext x
    constructor
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [hsub] at hxsub
      simpa using hxsub
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ D.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [← hsub] at hxsub
      simpa using hxsub
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun A hA => ?_
  have hmap : (A.subtype (fun x => x ∉ B)).map
      (Function.Embedding.subtype fun x : α => x ∉ B) = A :=
    Finset.subtype_map_of_mem (fun x hx => by
      have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
      simpa using hxcomp)
  have hcard : (A.subtype (fun x => x ∉ B)).card = A.card := by
    rw [← Finset.card_map (Function.Embedding.subtype fun x : α => x ∉ B), hmap]
  rw [hcard]

lemma prod_parts_eq_root_mul_avoid (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (∏ A : P.parts, C.counts A.val.card) =
      C.counts B.card * ∏ A : (P.avoid B).parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort P.parts (fun A : Finset α => C.counts A.card),
    Finset.prod_coe_sort (P.avoid B).parts (fun A : Finset α => C.counts A.card)]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  rw [hparts, Finset.prod_insert hBnot]

@[simp] lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ (rootBlockEquiv n S).val} : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin (n + 1))) \ (rootBlockEquiv n S).val := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
    rootBlockEquiv_card]
  omega

/-- The EGF of the derivative class is the formal derivative of the EGF. -/
theorem CombClass.egf_deriv (C : CombClass) :
    C.deriv.egf = d⁄dX ℚ C.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, coeff_derivative,
    CombClass.coeff_egf]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [Nat.factorial_succ, hn, hnf]
  rw [Nat.factorial_succ]
  push_cast
  ring_nf

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the "singletons-and-pairs" class is `z + z²/2`. -/
theorem CombClass.egf_parts12_egf :
    CombClass.parts12.egf = X + (2⁻¹ : ℚ) • X ^ 2 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts12, map_add, coeff_X, map_smul, coeff_X_pow,
    smul_eq_mul]
  rcases n with _ | _ | _ | m <;> norm_num [Nat.factorial] <;> omega

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- BGF transfer theorem for marked sequences

For an ordinary class `C`, `seqMarked C` is `SEQ(C)` with the sequence length
marked by the parameter variable `u`.  Its BGF satisfies
`F(z,u) = 1 / (1 - u C(z))`, represented here as
`F * (1 - u C(z)) = 1`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

lemma nat_smul_eq_rat_smul (m : ℕ) (p : ℚ[X]) :
    m • p = (m : ℚ) • p := by
  rw [nsmul_eq_mul]
  rw [show (m : ℚ[X]) = Polynomial.C (m : ℚ) by norm_num]
  rw [← Polynomial.smul_eq_C_mul]

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sequences

For a labelled class `C`, `lseqMarked C` is `SEQ(C)` with the number of
components marked by the parameter variable `u`.  Its bivariate EGF satisfies

  `F(z,u) = 1 / (1 - u C(z))`,

represented here as `F * (1 - u C(z)) = 1` over `ℚ[u]⟦z⟧`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] theorem ParamClass.coeff_begf (C : ParamClass) (n : ℕ) :
    PowerSeries.coeff n C.begf =
      ((n.factorial : ℚ)⁻¹) • C.paramPoly n := by
  rw [ParamClass.begf, PowerSeries.coeff_mk]

@[simp] theorem coeff_liftU (f : ℚ⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (liftU f) = Polynomial.C (PowerSeries.coeff n f) := by
  simp [liftU]

theorem coeff_U_liftU_egf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
      =
    Polynomial.X *
      Polynomial.C ((C.counts n : ℚ) / (n.factorial : ℚ)) := by
  simp [liftU, CombClass.coeff_egf]

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sets

For a labelled class `C`, `setMarked C` is `SET(C)` with the number of blocks
marked by the parameter variable `u`. Its bivariate EGF is

  `F(z,u) = exp(u C(z))`,

represented here as substitution into `PowerSeries.exp ℚ[X]`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem derivative_liftU (f : ℚ⟦X⟧) :
    d⁄dX ℚ[X] (liftU f) = liftU (d⁄dX ℚ f) := by
  ext n
  rw [coeff_derivative, coeff_liftU, coeff_liftU, coeff_derivative]
  simp [Polynomial.C_mul]

theorem derivative_U_liftU (f : ℚ⟦X⟧) :
    d⁄dX ℚ[X] (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU f) =
      PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ f) := by
  change PowerSeries.derivativeFun (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU f) = _
  rw [PowerSeries.derivativeFun_mul, PowerSeries.derivativeFun_C]
  rw [show PowerSeries.derivativeFun (liftU f) = liftU (d⁄dX ℚ f) by
    change d⁄dX ℚ[X] (liftU f) = liftU (d⁄dX ℚ f)
    exact derivative_liftU f]
  set_option backward.isDefEq.respectTransparency false in
    simp [smul_eq_mul]

lemma hasSubst_U_liftU_egf {C : CombClass} (hC : C.counts 0 = 0) :
    HasSubst (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) := by
  apply HasSubst.of_constantCoeff_zero'
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_U_liftU_egf, hC]
  simp

theorem subst_exp_ode_U_liftU {C : CombClass} (hC : C.counts 0 = 0) :
    d⁄dX ℚ[X]
        ((PowerSeries.exp ℚ[X]).subst
          (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        ((PowerSeries.exp ℚ[X]).subst
          (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) := by
  rw [derivative_subst (hg := hasSubst_U_liftU_egf hC),
    derivative_exp, derivative_U_liftU]
  set_option backward.isDefEq.respectTransparency false in
    ring

lemma ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull (C : CombClass) (n : ℕ) :
    (ParamClass.setMarked C).paramPoly n = setMarkedWeightFull C (Fin n) := by
  classical
  rw [ParamClass.paramPoly, ParamClass.setMarked]
  change (∑ x : Σ P : Finpartition (Finset.univ : Finset (Fin n)),
      ∀ B : P.parts, C.Obj B.val.card,
      (Polynomial.X : ℚ[X]) ^ x.1.parts.card) = _
  rw [Fintype.sum_sigma]
  unfold setMarkedWeightFull
  refine Finset.sum_congr rfl fun P _ => ?_
  change (∑ _y : ∀ B : P.parts, C.Obj B.val.card,
      (Polynomial.X : ℚ[X]) ^ P.parts.card) =
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi]
  rw [nat_smul_eq_rat_smul]
  rfl

lemma ParamClass.paramPoly_setMarked_zero (C : CombClass) :
    (ParamClass.setMarked C).paramPoly 0 = 1 := by
  classical
  rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
  unfold setMarkedWeightFull
  have huniv : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := by
    simp
  rw [huniv]
  rw [Fintype.sum_unique]
  let P : Finpartition (⊥ : Finset (Fin 0)) := default
  have hparts : P.parts = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro A hA
    exact P.ne_empty hA (by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxbot : x ∈ (⊥ : Finset (Fin 0)) := P.subset hA hx
      simp at hxbot)
  change (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card = 1
  rw [hparts]
  simp

@[simp] lemma finpartitionUnivCongr_parts_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (P : Finpartition (Finset.univ : Finset α)) :
    (finpartitionUnivCongr e P).parts.card = P.parts.card := by
  have h := Fintype.card_congr (finpartitionUnivCongrParts e P)
  simpa using h.symm

lemma prod_parts_finpartitionUnivCongr (C : CombClass)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (P : Finpartition (Finset.univ : Finset α)) :
    (∏ B : (finpartitionUnivCongr e P).parts, C.counts B.val.card) =
      ∏ B : P.parts, C.counts B.val.card := by
  symm
  exact Fintype.prod_equiv (M := ℕ) (finpartitionUnivCongrParts e P)
    (fun B : P.parts => C.counts B.val.card)
    (fun B : (finpartitionUnivCongr e P).parts => C.counts B.val.card)
    (fun B => by
      exact congrArg C.counts (finpartitionUnivCongrParts_card e P B).symm)

lemma setMarkedWeightFull_congr (C : CombClass)
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) :
    setMarkedWeightFull C α = setMarkedWeightFull C β := by
  classical
  unfold setMarkedWeightFull
  exact Fintype.sum_equiv (finpartitionUnivCongr e)
    (fun P : Finpartition (Finset.univ : Finset α) =>
      (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card)
    (fun P : Finpartition (Finset.univ : Finset β) =>
      (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card)
    (fun P => by
      dsimp
      have hprod := prod_parts_finpartitionUnivCongr C e P
      have hcard := finpartitionUnivCongr_parts_card e P
      have hprod_attach :
          ((finpartitionUnivCongr e P).parts.attach.prod fun i => C.counts i.val.card) =
            (P.parts.attach.prod fun i => C.counts i.val.card) := by
        simpa [Finset.prod_coe_sort] using hprod
      rw [hprod_attach, hcard])

lemma setMarkedWeightFull_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setMarkedWeightFull C α = setMarkedWeightFull C (Fin (Fintype.card α)) :=
  setMarkedWeightFull_congr C (Fintype.equivFin α)

lemma parts_card_sdiffSubtype {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (finpartitionSdiffSubtype B Q).parts.card = Q.parts.card := by
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : Set.InjOn (fun A : Finset α => A.subtype (fun x => x ∉ B)) Q.parts := by
    intro A hA D hD hsub
    change A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) at hsub
    ext x
    constructor
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [hsub] at hxsub
      simpa using hxsub
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ D.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [← hsub] at hxsub
      simpa using hxsub
  exact Finset.card_image_of_injOn hinj

lemma setMarkedWeightFinset_sdiff_eq_setMarkedWeightFull (C : CombClass) {α : Type*}
    [Fintype α] [DecidableEq α] (B : Finset α) :
    setMarkedWeightFinset C ((Finset.univ : Finset α) \ B) =
      setMarkedWeightFull C {x : α // x ∉ B} := by
  classical
  unfold setMarkedWeightFinset setMarkedWeightFull
  have hprod_rat :
      ∀ Q : Finpartition ((Finset.univ : Finset α) \ B),
        (∏ A : (finpartitionSdiffSubtype B Q).parts, (C.counts A.val.card : ℚ)) =
          ∏ A : Q.parts, (C.counts A.val.card : ℚ) := by
    intro Q
    exact_mod_cast prod_parts_sdiffSubtype C B Q
  exact Fintype.sum_equiv (finpartitionSdiffSubtypeCongr B)
    (fun Q : Finpartition ((Finset.univ : Finset α) \ B) =>
      (((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ Q.parts.card)
    (fun Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B}) =>
      (((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ Q.parts.card)
    (fun Q => by
      dsimp
      have hprod := prod_parts_sdiffSubtype C B Q
      have hcard := parts_card_sdiffSubtype B Q
      have hprod_attach :
          ((finpartitionSdiffSubtype B Q).parts.attach.prod fun i => C.counts i.val.card) =
            (Q.parts.attach.prod fun i => C.counts i.val.card) := by
        simpa [Finset.prod_coe_sort] using hprod
      change (((Q.parts.attach.prod fun A => C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ Q.parts.card =
        ((((finpartitionSdiffSubtype B Q).parts.attach.prod fun A =>
            C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ (finpartitionSdiffSubtype B Q).parts.card
      rw [hprod_attach, hcard])

lemma prod_parts_eq_root_mul_avoid_marked (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (((∏ A : P.parts, C.counts A.val.card) : ℕ) : ℚ) •
        (Polynomial.X : ℚ[X]) ^ P.parts.card =
      Polynomial.X * Polynomial.C (C.counts B.card : ℚ) *
        ((((∏ A : (P.avoid B).parts, C.counts A.val.card) : ℕ) : ℚ) •
          (Polynomial.X : ℚ[X]) ^ (P.avoid B).parts.card) := by
  rw [prod_parts_eq_root_mul_avoid C hB]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  have hcard : P.parts.card = (P.avoid B).parts.card + 1 := by
    rw [hparts, Finset.card_insert_of_notMem hBnot]
  rw [hcard, pow_succ]
  rw [show (((C.counts B.card * ∏ A : (P.avoid B).parts,
        C.counts A.val.card : ℕ) : ℚ) : ℚ) =
      (C.counts B.card : ℚ) *
        (((∏ A : (P.avoid B).parts, C.counts A.val.card) : ℕ) : ℚ) by
        norm_num]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [Polynomial.C_mul]
  ring_nf

lemma sum_finset_by_card_nsmul {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : ℕ → M) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k : Fin (n + 1), n.choose (k : ℕ) • f (k : ℕ) := by
  classical
  let len : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, by
      exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
  have hsplit :
      (∑ S : Finset (Fin n), f S.card) =
        ∑ x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}), f x.2.val.card := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv len)
      (fun x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}) =>
        f x.2.val.card)
      (fun S : Finset (Fin n) => f S.card)
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcard :
      Fintype.card {S : Finset (Fin n) // len S = k} = n.choose (k : ℕ) := by
    have hcard' :
        Fintype.card {S : Finset (Fin n) // len S = k} =
          (Fintype.card (Fin n)).choose (k : ℕ) := by
      rw [← Fintype.card_finset_len (α := Fin n) (k := (k : ℕ))]
      exact Fintype.card_congr
        { toFun := fun S => ⟨S.val, by
            have h := congrArg Fin.val S.property
            exact h⟩
          invFun := fun S => ⟨S.val, by
            apply Fin.ext
            exact S.property⟩
          left_inv := by intro S; apply Subtype.ext; rfl
          right_inv := by intro S; apply Subtype.ext; rfl }
    simpa [Fintype.card_fin] using hcard'
  trans Fintype.card {S : Finset (Fin n) // len S = k} • f (k : ℕ)
  · rw [← Finset.card_univ, Finset.sum_eq_card_nsmul]
    intro S _hS
    have h := congrArg Fin.val S.property
    simpa using congrArg f h
  · rw [hcard]

lemma setMarkedWeightFull_root (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) :
    setMarkedWeightFull C α =
      ∑ B : {B : Finset α // r ∈ B},
        Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
          setMarkedWeightFull C {x : α // x ∉ B.val} := by
  classical
  unfold setMarkedWeightFull
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, P.mem_part (by simp)⟩
  let w : Finpartition (Finset.univ : Finset α) → ℚ[X] :=
    fun P => (((∏ A : P.parts, C.counts A.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card
  have hsplit :
      ∑ P : Finpartition (Finset.univ : Finset α), w P =
        ∑ x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}), w x.2.val := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block)
      (fun x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}) => w x.2.val)
      w
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun B _ => ?_
  let fiberEquiv :
      {P : Finpartition (Finset.univ : Finset α) // block P = B} ≃
        {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} :=
    { toFun := fun P => ⟨P.val, by
        have h := congrArg Subtype.val P.property
        exact h⟩
      invFun := fun P => ⟨P.val, by
        apply Subtype.ext
        exact P.property⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  let rootEquiv := finpartitionRootFiberEquiv r B.property
  have hfiber :
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val =
        ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
          Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
            ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
              (Polynomial.X : ℚ[X]) ^ Q.parts.card) := by
    calc
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val
          = ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val},
              w P.val := by
            exact Fintype.sum_equiv fiberEquiv
              (fun P => w P.val) (fun P => w P.val) (by intro P; rfl)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              w ((rootEquiv.symm Q).val) := by
            exact Fintype.sum_equiv rootEquiv
              (fun P => w P.val)
              (fun Q => w ((rootEquiv.symm Q).val))
              (by intro P; simp)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
                ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
                  (Polynomial.X : ℚ[X]) ^ Q.parts.card) := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            have hruniv : r ∈ (Finset.univ : Finset α) := by simp
            have hBmem : B.val ∈ (rootEquiv.symm Q).val.parts := by
              have hprop := (rootEquiv.symm Q).property
              simpa [hprop] using (rootEquiv.symm Q).val.part_mem.2 hruniv
            dsimp [w]
            change (((∏ A : (rootEquiv.symm Q).val.parts, C.counts A.val.card) : ℕ) : ℚ) •
                (Polynomial.X : ℚ[X]) ^ (rootEquiv.symm Q).val.parts.card =
              Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
                ((((∏ A : Q.parts, C.counts A.val.card) : ℕ) : ℚ) •
                  (Polynomial.X : ℚ[X]) ^ Q.parts.card)
            rw [prod_parts_eq_root_mul_avoid_marked C hBmem]
            have havoid : (rootEquiv.symm Q).val.avoid B.val = Q := by
              exact Equiv.apply_symm_apply rootEquiv Q
            rw [havoid]
  rw [hfiber]
  rw [← Finset.mul_sum]
  change Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
      setMarkedWeightFinset C ((Finset.univ : Finset α) \ B.val) =
    Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
      setMarkedWeightFull C {x : α // x ∉ B.val}
  rw [setMarkedWeightFinset_sdiff_eq_setMarkedWeightFull]

lemma ParamClass.paramPoly_setMarked_succ (C : CombClass) (n : ℕ) :
    (ParamClass.setMarked C).paramPoly (n + 1) =
      ∑ k : Fin (n + 1),
        Polynomial.X *
          Polynomial.C
            (((n.choose (k : ℕ) * C.counts ((k : ℕ) + 1) : ℕ) : ℚ)) *
          (ParamClass.setMarked C).paramPoly (n - (k : ℕ)) := by
  classical
  rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
  rw [setMarkedWeightFull_root C (Fin.last n)]
  have hblocks :
      (∑ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
          Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
            setMarkedWeightFull C {x : Fin (n + 1) // x ∉ B.val})
        =
      ∑ S : Finset (Fin n),
        Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
          (ParamClass.setMarked C).paramPoly (n - S.card) := by
    symm
    exact Fintype.sum_equiv (rootBlockEquiv n)
      (fun S : Finset (Fin n) =>
        Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
          (ParamClass.setMarked C).paramPoly (n - S.card))
      (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
        Polynomial.X * Polynomial.C (C.counts B.val.card : ℚ) *
          setMarkedWeightFull C {x : Fin (n + 1) // x ∉ B.val})
      (by
        intro S
        change Polynomial.X * Polynomial.C (C.counts (S.card + 1) : ℚ) *
            (ParamClass.setMarked C).paramPoly (n - S.card) =
          Polynomial.X * Polynomial.C (C.counts ((rootBlockEquiv n S).val.card) : ℚ) *
            setMarkedWeightFull C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}
        rw [rootBlockEquiv_card]
        rw [ParamClass.paramPoly_setMarked_eq_setMarkedWeightFull]
        rw [setMarkedWeightFull_card C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}]
        rw [rootBlockEquiv_compl_card])
  rw [hblocks]
  rw [sum_finset_by_card_nsmul n
    (fun k => Polynomial.X * Polynomial.C (C.counts (k + 1) : ℚ) *
      (ParamClass.setMarked C).paramPoly (n - k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nat_smul_eq_rat_smul, Polynomial.smul_eq_C_mul]
  have hcast : (((n.choose (k : ℕ) * C.counts ((k : ℕ) + 1) : ℕ) : ℚ) =
      (n.choose (k : ℕ) : ℚ) * (C.counts ((k : ℕ) + 1) : ℚ)) := by
    norm_num
  rw [hcast]
  rw [Polynomial.C_mul]
  ring

theorem ParamClass.coeff_derivative_begf (P : ParamClass) (n : ℕ) :
    PowerSeries.coeff n (d⁄dX ℚ[X] P.begf) =
      ((n.factorial : ℚ)⁻¹) • P.paramPoly (n + 1) := by
  rw [coeff_derivative, ParamClass.coeff_begf]
  have hscalar :
      (((n + 1).factorial : ℚ)⁻¹ * ((n + 1 : ℕ) : ℚ)) =
        (n.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ]
    have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hn, hnf]
    norm_num [Nat.cast_mul]
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  rw [show ((n : ℚ[X]) + 1) = Polynomial.C ((n + 1 : ℕ) : ℚ) by norm_num]
  calc
    Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
          P.paramPoly (n + 1) * Polynomial.C ((n + 1 : ℕ) : ℚ)
        = Polynomial.C ((((n + 1).factorial : ℚ)⁻¹ * ((n + 1 : ℕ) : ℚ))) *
            P.paramPoly (n + 1) := by
          rw [show Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
              P.paramPoly (n + 1) * Polynomial.C ((n + 1 : ℕ) : ℚ) =
              (Polynomial.C (((n + 1).factorial : ℚ)⁻¹) *
                Polynomial.C ((n + 1 : ℕ) : ℚ)) * P.paramPoly (n + 1) by ring]
          rw [Polynomial.C_mul]
    _ = Polynomial.C ((n.factorial : ℚ)⁻¹) * P.paramPoly (n + 1) := by
          rw [hscalar]

theorem coeff_U_liftU_derivative_egf (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) =
  Polynomial.X *
      Polynomial.C ((C.counts (n + 1) : ℚ) / (n.factorial : ℚ)) := by
  rw [← CombClass.egf_deriv C]
  simp [CombClass.counts_deriv]

private lemma factorial_choose_scalar_set (n k a : ℕ) (hk : k ≤ n) :
    (a : ℚ) / (k.factorial : ℚ) * (((n - k).factorial : ℚ)⁻¹) =
      (((n.choose k * a : ℕ) : ℚ) * ((n.factorial : ℚ)⁻¹)) := by
  have hchooseQ : (((n.choose k : ℚ) * (k.factorial : ℚ) *
      ((n - k).factorial : ℚ)) = (n.factorial : ℚ)) := by
    have hnat := Nat.choose_mul_factorial_mul_factorial hk
    exact_mod_cast hnat
  have hkfac : ((k.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hnkfac : (((n - k).factorial : ℚ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hnfac : ((n.factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hkfac, hnkfac, hnfac]
  norm_num
  rw [← hchooseQ]
  ring

private lemma invFactorial_smul_C_X_eq_set
    (C : CombClass) (n k : ℕ) (p : ℚ[X]) (hk : k ≤ n) :
    (((n - k).factorial : ℚ)⁻¹) •
        (Polynomial.X *
          Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p) =
      ((n.factorial : ℚ)⁻¹) •
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
  have hscalar := factorial_choose_scalar_set n k (C.counts (k + 1)) hk
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul]
  calc
    Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p)
        = Polynomial.C (((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) *
            (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [show Polynomial.C (((n - k).factorial : ℚ)⁻¹) *
              ((Polynomial.X : ℚ[X]) *
                Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) * p) =
              (Polynomial.C ((C.counts (k + 1) : ℚ) / (k.factorial : ℚ)) *
                Polynomial.C (((n - k).factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]
    _ = Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ) *
            ((n.factorial : ℚ)⁻¹)) * (Polynomial.X * p) := by
          rw [hscalar]
    _ = Polynomial.C ((n.factorial : ℚ)⁻¹) *
        ((Polynomial.X : ℚ[X]) *
          Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) := by
          rw [show Polynomial.C ((n.factorial : ℚ)⁻¹) *
              ((Polynomial.X : ℚ[X]) *
                Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) * p) =
              (Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) *
                Polynomial.C ((n.factorial : ℚ)⁻¹)) * (Polynomial.X * p) by ring]
          rw [Polynomial.C_mul]

private lemma mul_invFactorial_smul_assoc_set (a b : ℚ) (p : ℚ[X]) :
    (Polynomial.X : ℚ[X]) * Polynomial.C a * (b • p) =
      b • ((Polynomial.X : ℚ[X]) * Polynomial.C a * p) := by
  rw [Polynomial.smul_eq_C_mul]
  rw [Polynomial.smul_eq_C_mul]
  ring

private lemma coeff_U_liftU_derivative_mul_setMarked_begf
    (C : CombClass) (n : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        (ParamClass.setMarked C).begf)
      =
    ((n.factorial : ℚ)⁻¹) •
      (ParamClass.setMarked C).paramPoly (n + 1) := by
  classical
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [ParamClass.paramPoly_setMarked_succ C n, Finset.smul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => ((n.factorial : ℚ)⁻¹) •
      ((Polynomial.X : ℚ[X]) *
        Polynomial.C (((n.choose k * C.counts (k + 1) : ℕ) : ℚ)) *
        (ParamClass.setMarked C).paramPoly (n - k))) (n + 1)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [coeff_U_liftU_derivative_egf, ParamClass.coeff_begf]
  rw [mul_invFactorial_smul_assoc_set]
  exact invFactorial_smul_C_X_eq_set C n k
    ((ParamClass.setMarked C).paramPoly (n - k)) hk

theorem ParamClass.begf_setMarked_ode (C : CombClass) :
    d⁄dX ℚ[X] (ParamClass.setMarked C).begf =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) *
        (ParamClass.setMarked C).begf := by
  apply PowerSeries.ext
  intro n
  rw [ParamClass.coeff_derivative_begf,
    coeff_U_liftU_derivative_mul_setMarked_begf]

theorem ParamClass.begf_setMarked_exp (C : CombClass) (hC : C.counts 0 = 0) :
    (ParamClass.setMarked C).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) := by
  let H : ℚ[X]⟦X⟧ :=
    (ParamClass.setMarked C).begf -
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
  have hode : d⁄dX ℚ[X] H =
      (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) * H := by
    dsimp [H]
    rw [map_sub, ParamClass.begf_setMarked_ode,
      subst_exp_ode_U_liftU hC]
    set_option backward.isDefEq.respectTransparency false in
      ring
  have h0C : constantCoeff (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_U_liftU_egf, hC]
    simp
  have h0set : constantCoeff (ParamClass.setMarked C).begf = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ParamClass.coeff_begf,
      ParamClass.paramPoly_setMarked_zero]
    simp
  have h0subst :
      constantCoeff ((PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)) = 1 := by
    change MvPowerSeries.constantCoeff
      (PowerSeries.subst (PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf)
        (PowerSeries.exp ℚ[X])) = 1
    rw [constantCoeff_subst (hasSubst_U_liftU_egf hC)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      have hpow : MvPowerSeries.constantCoeff
          ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) ^ d) = 0 := by
        change constantCoeff
          ((PowerSeries.C (Polynomial.X : ℚ[X]) * liftU C.egf) ^ d) = 0
        rw [map_pow, h0C, zero_pow hd]
      set_option backward.isDefEq.respectTransparency false in
        rw [hpow, smul_zero]
  have h0 : constantCoeff H = 0 := by
    dsimp [H]
    rw [map_sub, h0set, h0subst, sub_self]
  have hH : H = 0 := ode_unique (H := H)
    (G := PowerSeries.C (Polynomial.X : ℚ[X]) * liftU (d⁄dX ℚ C.egf)) hode h0
  exact sub_eq_zero.mp hH

end AnalyticCombinatorics.Ch1

/-!
# Ch3 -- Bivariate EGF applications for marked labelled sets

Cheap specializations of `ParamClass.begf_setMarked_exp` for the standard
labelled examples from Chapter 2.
-/

open scoped Polynomial

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open scoped Polynomial
theorem solution :
    (ParamClass.setMarked CombClass.parts12).begf =
      (PowerSeries.exp ℚ[X]).subst
        (PowerSeries.C (Polynomial.X : ℚ[X]) *
          liftU (PowerSeries.X + (2⁻¹ : ℚ) • PowerSeries.X ^ 2)) := by
  have h := ParamClass.begf_setMarked_exp CombClass.parts12
    (by simp [CombClass.counts_parts12])
  rwa [CombClass.egf_parts12_egf] at h
