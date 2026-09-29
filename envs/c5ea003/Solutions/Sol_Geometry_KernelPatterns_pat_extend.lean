-- Prove2me | solution 1 for Geometry.KernelPatterns.pat_extend
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:36:59.809462+00:00
-- url     : https://prove2.me/submissions/e2c0b823-d70d-4cdb-ac75-cb85ac7d0b8c

-- Sol generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_pat_eq_self_iff

/-!
# Kernel patterns with a prescribed number of blocks are the Stirling numbers

Mathlib defines the Stirling numbers of the second kind `Nat.stirlingSecond`
purely by their recursion.  Here we prove that they really do count kernel
patterns: the number of equality patterns of `n`-tuples having exactly `k`
distinct values is `Nat.stirlingSecond n k`
(`card_patternsWith_eq_stirlingSecond`).

The proof is a structural induction implemented by an explicit
restriction/extension dictionary between patterns on `Fin (n+1)` and patterns on
`Fin n`:

* `restr p` — delete the last index;
* `extend q a` — re-attach a last index whose representative is `a`;
* `extend_restr`, `restr_extend` — these are mutually inverse.

Deleting the last index either destroys a singleton block (`p` fixes the last
index) or leaves the block structure unchanged (`p` sends it into one of the
`k` existing blocks), which is exactly the Stirling recursion
`S(n+1, k+1) = (k+1) * S(n, k+1) + S(n, k)`.
-/

open Geometry.KernelPatterns

open Finset

variable {n : ℕ}

/-! ### A pointwise characterisation of patterns -/



/-! ### Deleting and re-attaching the last index -/



@[simp] lemma extend_castSucc (q : Fin n → Fin n) (a : Fin (n + 1)) (i : Fin n) :
    extend q a i.castSucc = (q i).castSucc := by
  simp only [extend, Fin.val_castSucc, i.isLt, dif_pos]

@[simp] lemma extend_last (q : Fin n → Fin n) (a : Fin (n + 1)) :
    extend q a (Fin.last n) = a := by
  simp [extend]






/-! ### How the block count changes -/





/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/







open Geometry.KernelPatterns in
theorem solution{q : Fin n → Fin n} (hq : pat q = q) {a : Fin (n + 1)}
    (ha : a = Fin.last n ∨ ∃ w : Fin n, q w = w ∧ a = w.castSucc) :
    pat (extend q a) = extend q a := by
  obtain ⟨hle, hidem⟩ := (pat_eq_self_iff q).1 hq
  refine (pat_eq_self_iff _).2 ⟨fun j => ?_, fun j => ?_⟩
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [extend_castSucc]
      exact Fin.castSucc_le_castSucc_iff.2 (hle i)
    · rw [extend_last]
      exact Fin.le_last a
  · rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · rw [extend_castSucc, extend_castSucc, hidem]
    · rw [extend_last]
      rcases ha with rfl | ⟨w, hw, rfl⟩
      · rw [extend_last]
      · rw [extend_castSucc, hw]
