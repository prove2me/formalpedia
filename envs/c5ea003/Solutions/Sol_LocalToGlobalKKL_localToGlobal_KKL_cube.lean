-- Prove2me | solution 1 for LocalToGlobalKKL.localToGlobal_KKL_cube
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:32:54.979146+00:00
-- url     : https://prove2.me/submissions/f85c34b1-c787-41ee-9508-86167f554cf8

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


/-- **Local-to-global decomposition of total influence.**  Summing the bridge over
all coordinates other than the pinned coordinate `j`, the global total influence
(excluding `j`) equals the sum of the two links' total influences. -/
theorem linktot_decomp (f : (Fin n → Bool) → Bool) (j : Fin n) :
    ∑ i ∈ univ.erase j, Inf f i = LinkTotInf f j false + LinkTotInf f j true := by
  unfold LinkTotInf
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; exact inf_decomp f j i

/-! ### Pigeonhole: some coordinate carries at least the average influence -/

/-- Over a finite set some element attains at least the average of a `ℕ`-valued
function. -/
lemma exists_ge_avg_nat {ι : Type*} (s : Finset ι) (g : ι → ℕ) (hs : s.Nonempty) :
    ∃ i ∈ s, ∑ j ∈ s, g j ≤ s.card * g i := by
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image g hs
  refine ⟨i, hi, ?_⟩
  calc ∑ j ∈ s, g j ≤ ∑ _j ∈ s, g i := Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = s.card * g i := by rw [Finset.sum_const, smul_eq_mul]




/-! ## Abstract engine: local KKL ⟹ global KKL -/






/-! ## The Boolean cube as an instance of the abstract engine -/



open LocalToGlobalKKL in
theorem solution(f : (Fin n → Bool) → Bool) (j : Fin n)
    (hn : 2 ≤ n) (T : ℕ)
    (hfalse : T ≤ LinkTotInf f j false) (htrue : T ≤ LinkTotInf f j true) :
    ∃ i ∈ univ.erase j, 2 * T ≤ (n - 1) * Inf f i := by
  have hne : (univ.erase j : Finset (Fin n)).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ j),
        Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i, hi, hle⟩ := exists_ge_avg_nat (univ.erase j) (Inf f) hne
  refine ⟨i, hi, ?_⟩
  have hcard : (univ.erase j : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hsum : 2 * T ≤ ∑ i ∈ univ.erase j, Inf f i := by
    rw [linktot_decomp]; omega
  calc 2 * T ≤ ∑ i ∈ univ.erase j, Inf f i := hsum
    _ ≤ (univ.erase j).card * Inf f i := hle
    _ = (n - 1) * Inf f i := by rw [hcard]
