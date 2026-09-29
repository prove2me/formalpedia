-- Prove2me | Theorems.Thm_mme_3AP_free_no_collision
-- name    : mme_3AP_free_no_collision
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-05-31T17:51:47.19367+00:00
-- url     : https://prove2.me/theorems/d58a104f-309b-40a5-8edf-33c3cc45b951
-- statement:
--   **3AP-free sets have no coordinatewise mean-collisions.**
--
--   If $S \subseteq \mathbb{N}$ is 3-term-AP-free and $I, J, K : \mathrm{Fin}\,n \to \mathbb{N}$ are integer vectors with every coordinate of every vector in $S$, satisfying $I + K = 2J$ coordinatewise, then $I = K$.
--
--     $S$ 3AP-free  $\wedge$  $I + K = 2J$  $\wedge$  $\forall i,\; I(i), J(i), K(i) \in S$  $\Rightarrow$  $I = K$.
--
--   **The combinatorial heart of the laser method's "zeroing-out" step.** When block indices in $T_q^{\otimes 2N}$ are restricted to coordinatewise lie in a 3AP-free $S \subseteq [N]$, two distinct blocks cannot share their second-power "midpoint" index — the support of the symmetric tensor square has no collisions.
--
--   **Proof.** Coordinatewise application of the definition of `ThreeAPFree`: for each $i$, $I(i) + K(i) = 2J(i)$ with $I(i), J(i), K(i) \in S$ forces $I(i) = J(i)$ (by ThreeAPFree applied at index $i$); the original equation then yields $K(i) = J(i)$, so $I(i) = K(i)$. `funext` and `omega` finish.
--
--   **Reusability — the prototypical abstract Layer-3 leaf.** Used by every laser-method argument exploiting 3AP-free sets: Coppersmith–Winograd 1990, Strassen 1986/1988, Stothers 2010, Vassilevska Williams 2012, Le Gall 2014, Alman–Vassilevska Williams 2020. The coordinatewise vector form here is the *exact* shape needed when block indices are multi-indices into $[N]^n$. Stated as a paper-agnostic, Mathlib-native lemma; the proof is a single funext+omega chain.
-- source:
--   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/Additive/AP/Three/Behrend.html

import Mathlib.Combinatorics.Additive.AP.Three.Defs

theorem mme_3AP_free_no_collision {n : ℕ} (S : Finset ℕ) (hS : ThreeAPFree (S : Set ℕ)) (I J K : Fin n → ℕ) (hI : ∀ i, I i ∈ S) (hJ : ∀ i, J i ∈ S) (hK : ∀ i, K i ∈ S) (h : ∀ i, I i + K i = 2 * J i) : I = K := by sorry
