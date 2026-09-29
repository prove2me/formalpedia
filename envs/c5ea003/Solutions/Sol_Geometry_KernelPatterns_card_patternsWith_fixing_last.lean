-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patternsWith_fixing_last
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:39:10.542026+00:00
-- url     : https://prove2.me/submissions/7ab8cfb4-5926-4f05-9129-1e5477d7d9f0

-- Sol generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Theorems.Thm_Geometry_KernelPatterns_image_extend_last
import Theorems.Thm_Geometry_KernelPatterns_mem_patternsWith
import Theorems.Thm_Geometry_KernelPatterns_pat_eq_self_iff
import Theorems.Thm_Geometry_KernelPatterns_pat_extend
import Theorems.Thm_Geometry_KernelPatterns_pat_restr

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

@[simp] lemma restr_extend (q : Fin n → Fin n) (a : Fin (n + 1)) :
    restr (extend q a) = q := by
  funext i
  simp only [restr, extend_castSucc, Fin.val_castSucc]
  rw [dif_pos (q i).isLt]

lemma extend_restr {p : Fin (n + 1) → Fin (n + 1)} (hp : pat p = p) :
    extend (restr p) (p (Fin.last n)) = p := by
  have hle := ((pat_eq_self_iff p).1 hp).1
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · have hlt : (p i.castSucc : ℕ) < n := lt_of_le_of_lt (hle i.castSucc) i.isLt
    rw [extend_castSucc]
    apply Fin.ext
    simp only [restr, dif_pos hlt, Fin.val_castSucc]
  · rw [extend_last]




/-! ### How the block count changes -/



lemma card_image_extend_last (q : Fin n → Fin n) :
    (univ.image (extend q (Fin.last n))).card = (univ.image q).card + 1 := by
  rw [image_extend_last]
  have hnot : Fin.last n ∉ (univ.image q).image Fin.castSucc := by simp
  have hcast : ((univ.image q).image Fin.castSucc).card = (univ.image q).card :=
    Finset.card_image_of_injective _ (Fin.castSucc_injective n)
  have hdisj : Disjoint ((univ.image q).image Fin.castSucc)
      ({Fin.last n} : Finset (Fin (n + 1))) := by
    simp [Finset.disjoint_singleton_right]
  rw [Finset.card_union_of_disjoint hdisj, hcast, Finset.card_singleton]


/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/







open Geometry.KernelPatterns in
theorem solution(n k : ℕ) :
    ((patternsWith (n + 1) (k + 1)).filter fun p => p (Fin.last n) = Fin.last n).card
      = (patternsWith n k).card := by
  refine Finset.card_bij' (fun p _ => restr p) (fun q _ => extend q (Fin.last n)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, mem_patternsWith] at hp
    obtain ⟨⟨hpat, hcard⟩, hlast⟩ := hp
    refine (mem_patternsWith _).2 ⟨pat_restr hpat, ?_⟩
    show (univ.image (restr p)).card = k
    have hp' : extend (restr p) (Fin.last n) = p := by
      rw [← hlast]; exact extend_restr hpat
    have hcnt := card_image_extend_last (restr p)
    rw [hp', hcard] at hcnt
    omega
  · intro q hq
    rw [mem_patternsWith] at hq
    refine Finset.mem_filter.2 ⟨(mem_patternsWith _).2 ⟨pat_extend hq.1 (Or.inl rfl), ?_⟩, ?_⟩
    · show (univ.image (extend q (Fin.last n))).card = k + 1
      rw [card_image_extend_last, hq.2]
    · show extend q (Fin.last n) (Fin.last n) = Fin.last n
      rw [extend_last]
  · intro p hp
    simp only [Finset.mem_filter, mem_patternsWith] at hp
    show extend (restr p) (Fin.last n) = p
    rw [← hp.2]
    exact extend_restr hp.1.1
  · intro q _
    exact restr_extend q (Fin.last n)
