-- Prove2me | Theorems.Thm_YogeshwaranDM_sdr_iff
-- name    : YogeshwaranDM.sdr_iff
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:43:55.685474+00:00
-- url     : https://prove2.me/theorems/9bf4e313-af73-4444-ba11-4726d04fd35d
-- title:
--   Corollary 6.9 — Systems of distinct representatives
-- statement:
--   **Corollary 6.9 — Systems of distinct representatives.** Let $I$ be a finite index set and let $(A_i)_{i\in I}$ be any family of sets in an ambient set $X$. The individual sets $A_i$ are not required to be finite. A **system of distinct representatives** is an injective function $f:I\to X$ with $f(i)\in A_i$ for every $i$, as in Definition 6.8. Then
--   $$
--   \bigl(\exists f:I\to X,\ f\text{ injective and }\forall i,\ f(i)\in A_i\bigr)
--   \quad\Longleftrightarrow\quad
--   \forall J\subseteq I,\ |J|\le\left|\bigcup_{i\in J}A_i\right|.
--   $$
--   The empty family is allowed.
--
--   **Formalization note.** The arbitrary sets use Set rather than Finset. Set.encard takes values in the extended natural numbers, so an infinite union has cardinality infinity and does not incorrectly become zero. Only the index family is assumed finite.
-- source:
--   D. Yogeshwaran, Discrete Mathematics—Lecture Notes, Indian Statistical Institute Bangalore, HTML edition generated May 9, 2025, Corollary 6.9, https://www.isibang.ac.in/~d.yogesh/Course_Notes/DM1/Ch6.S1.html

import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option autoImplicit false

namespace YogeshwaranDM

theorem sdr_iff {ι α : Type*} [Fintype ι] (A : ι → Set α) :
    (∃ f : ι → α, Function.Injective f ∧ ∀ i, f i ∈ A i) ↔
      ∀ I : Finset ι, (I.card : ℕ∞) ≤ (⋃ i ∈ I, A i).encard := by sorry

end YogeshwaranDM
