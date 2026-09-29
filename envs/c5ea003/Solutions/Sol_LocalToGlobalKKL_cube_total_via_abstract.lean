-- Prove2me | solution 1 for LocalToGlobalKKL.cube_total_via_abstract
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:14:40.993621+00:00
-- url     : https://prove2.me/submissions/781c1ea9-4fe4-4b52-9b26-9a2385a2f075

-- Sol generated from Cryptography/LocalToGlobalKKL/Basic.lean
import Mathlib
import Definitions.Def_Cryptography_LocalToGlobalKKL_Basic

/-!
# A Local-to-Global KKL Theorem for Influence Functions

This file develops a *local-to-global* principle for coordinate influences, in the
spirit of the Kahn–Kalai–Linial (KKL) theorem and the high-dimensional-expander
"local-to-global" machinery (Kahn–Kalai–Linial 1988; Bafna–Hoory–Kaufman 2022;
Gur–Lifshitz–Liu 2022; Gotlib–Kaufman 2023).

The KKL theorem is a *local* statement about a single Boolean function: any
non-degenerate low-influence function must have a coordinate of large influence.
The **local-to-global** paradigm asks: if the *links* of a simplicial complex each
satisfy a KKL-type property, does the whole complex satisfy a global KKL-type
property?  The engine that makes this work is that **influences self-average over
links**: the global influence of a coordinate is a (weighted) average of its
influences in the links.

We formalise two layers.

## Concrete model: the Boolean cube and its codimension-one links

For `f : (Fin n → Bool) → Bool` we define the (unnormalised) coordinate influence
`Inf f i` as the number of edges of the hypercube in direction `i` on which `f`
changes value.  Fixing a coordinate `j` and a value `b` cuts the cube into a
subcube — the *link* of the vertex `(j, b)` — and `InfSub f j b i` counts the
sensitive `i`-edges inside that subcube.  The key structural fact
(`inf_decomp`) is that

  `Inf f i = InfSub f j false i + InfSub f j true i`,

i.e. every influence splits as the sum of the influences in the two links.
Summing over coordinates gives the local-to-global decomposition
`linktot_decomp`, and combined with pigeonholing we obtain the flagship
concrete statement `localToGlobal_KKL_cube`: if both links of `j` carry total
influence `≥ T`, then some global coordinate has influence `≥ 2T/(n-1)`.

## Abstract engine: local KKL ⟹ global KKL

`abstract_localToGlobal_KKL` isolates the general averaging argument for an
arbitrary weighted family of links: given the self-averaging *bridge*
`I i = ∑ ℓ, w ℓ * Iℓ ℓ i` and the *local KKL hypothesis* that every link has an
influential coordinate (`∃ i, τ ≤ Iℓ ℓ i`), the global total influence is at
least `τ · (∑ ℓ w ℓ)`, and consequently (`abstract_global_influential_coord`)
some global coordinate has influence at least the average `τ·(∑ w)/|ι|`.

Finally `cube_total_via_abstract` shows the concrete Boolean-cube decomposition is
literally an instance of the abstract engine (two links of weight one).
-/

open LocalToGlobalKKL

open Finset

/-! ## Concrete model: the Boolean hypercube -/


variable {n : ℕ}








/-- **Influence self-averaging (the local-to-global bridge).**
Every coordinate influence splits as the sum of the two link influences.
This is the structural identity that powers the whole file. -/
theorem inf_decomp (f : (Fin n → Bool) → Bool) (j i : Fin n) :
    Inf f i = InfSub f j false i + InfSub f j true i := by
  unfold Inf InfSub
  rw [add_comm, ← Finset.card_filter_add_card_filter_not
      (s := univ.filter (fun x => f x ≠ f (flipc x i))) (p := fun x => x j = true)]
  rw [Finset.filter_filter, Finset.filter_filter]
  congr 1
  · congr 1; apply filter_congr; intro x _; simp [and_comm]
  · congr 1; apply filter_congr; intro x _; simp [and_comm, Bool.not_eq_true]



/-! ### Pigeonhole: some coordinate carries at least the average influence -/





/-! ## Abstract engine: local KKL ⟹ global KKL -/


/-- **Abstract local-to-global KKL theorem.**

Consider a system of coordinates `ι`, a weighted family of links `κ` with
non-negative weights `w`, non-negative local influences `Iℓ`, and global
influences `I`.  Assume:

* the **bridge** (influence self-averaging):  `I i = ∑ ℓ, w ℓ * Iℓ ℓ i`;
* the **local KKL hypothesis**: every link `ℓ` has an influential coordinate,
  `∃ i, τ ≤ Iℓ ℓ i`  (the KKL conclusion, applied on each link).

Then the **global total influence** is at least `τ · (∑ ℓ w ℓ)`.  This is the
purely combinatorial heart of every local-to-global argument for influences. -/
theorem abstract_localToGlobal_KKL
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (I : ι → ℝ) (w : κ → ℝ) (Iℓ : κ → ι → ℝ) (τ : ℝ)
    (hw : ∀ l, 0 ≤ w l) (hIℓ : ∀ l i, 0 ≤ Iℓ l i)
    (bridge : ∀ i, I i = ∑ l, w l * Iℓ l i)
    (localKKL : ∀ l, ∃ i, τ ≤ Iℓ l i) :
    τ * (∑ l, w l) ≤ ∑ i, I i := by
  have step : ∑ i, I i = ∑ l, w l * (∑ i, Iℓ l i) := by
    simp_rw [bridge]; rw [Finset.sum_comm]; congr 1; ext l; rw [Finset.mul_sum]
  rw [step, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  obtain ⟨i₀, hi₀⟩ := localKKL l
  have htot : τ ≤ ∑ i, Iℓ l i :=
    le_trans hi₀ (Finset.single_le_sum (fun i _ => hIℓ l i) (Finset.mem_univ i₀))
  rw [mul_comm τ (w l)]
  exact mul_le_mul_of_nonneg_left htot (hw l)




/-! ## The Boolean cube as an instance of the abstract engine -/



open LocalToGlobalKKL in
theorem solution{n : ℕ} (f : (Fin n → Bool) → Bool) (j : Fin n)
    (T : ℕ)
    (hfalse : ∃ i, T ≤ InfSub f j false i) (htrue : ∃ i, T ≤ InfSub f j true i) :
    2 * T ≤ TotInf f := by
  -- Instantiate the abstract engine with `κ = Bool`, weights `1`, `τ = T`.
  have key : (T : ℝ) * (∑ _l : Bool, (1 : ℝ)) ≤ ∑ i, (Inf f i : ℝ) := by
    refine abstract_localToGlobal_KKL (ι := Fin n) (κ := Bool)
      (fun i => (Inf f i : ℝ)) (fun _ => (1 : ℝ))
      (fun b i => (InfSub f j b i : ℝ)) (T : ℝ)
      (fun _ => by norm_num) (fun _ _ => by positivity) ?_ ?_
    · intro i
      have := inf_decomp f j i
      rw [Fintype.sum_bool]
      push_cast [this]; ring
    · intro l
      cases l with
      | false =>
          obtain ⟨i, hi⟩ := hfalse
          exact ⟨i, by show (T : ℝ) ≤ (InfSub f j false i : ℝ); exact_mod_cast hi⟩
      | true =>
          obtain ⟨i, hi⟩ := htrue
          exact ⟨i, by show (T : ℝ) ≤ (InfSub f j true i : ℝ); exact_mod_cast hi⟩
  have hsum : (∑ i, (Inf f i : ℝ)) = (TotInf f : ℝ) := by
    unfold TotInf; push_cast; ring
  rw [Fintype.sum_bool, hsum] at key
  have h2 : ((2 * T : ℕ) : ℝ) ≤ (TotInf f : ℝ) := by push_cast; linarith
  exact_mod_cast h2
