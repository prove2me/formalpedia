-- Prove2me | solution 1 for Geometry.KernelPatterns.pat_restr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:37:00.296063+00:00
-- url     : https://prove2.me/submissions/712fda92-32c7-41fb-a760-3faeb2f13530

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







lemma restr_apply_val {p : Fin (n + 1) → Fin (n + 1)} (hp : pat p = p) (i : Fin n) :
    (restr p i : ℕ) = (p i.castSucc : ℕ) := by
  have hle := ((pat_eq_self_iff p).1 hp).1
  have hlt : (p i.castSucc : ℕ) < n := lt_of_le_of_lt (hle i.castSucc) i.isLt
  simp only [restr, dif_pos hlt]



/-! ### How the block count changes -/





/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/







open Geometry.KernelPatterns in
theorem solution{p : Fin (n + 1) → Fin (n + 1)} (hp : pat p = p) :
    pat (restr p) = restr p := by
  obtain ⟨hle, hidem⟩ := (pat_eq_self_iff p).1 hp
  refine (pat_eq_self_iff _).2 ⟨fun i => ?_, fun i => ?_⟩
  · have h1 : (restr p i : ℕ) = (p i.castSucc : ℕ) := restr_apply_val hp i
    have h2 : (p i.castSucc : ℕ) ≤ (i : ℕ) := hle i.castSucc
    exact Fin.le_def.2 (by omega)
  · apply Fin.ext
    have h1 : (restr p i : ℕ) = (p i.castSucc : ℕ) := restr_apply_val hp i
    have h2 : (restr p (restr p i) : ℕ) = (p (restr p i).castSucc : ℕ) :=
      restr_apply_val hp _
    have h3 : ((restr p i).castSucc : Fin (n + 1)) = p i.castSucc := Fin.ext (by simpa using h1)
    rw [h2, h3, hidem]
    exact h1.symm
