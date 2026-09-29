-- Prove2me | solution 1 for Geometry.KernelPatterns.card_patternsWith_moving_last
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:39:11.065007+00:00
-- url     : https://prove2.me/submissions/ce908a2d-3f2f-43ac-9711-dd022ed702b1

-- Sol generated from Geometry/KernelPatterns/Stirling.lean
import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
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

lemma restr_apply_val {p : Fin (n + 1) → Fin (n + 1)} (hp : pat p = p) (i : Fin n) :
    (restr p i : ℕ) = (p i.castSucc : ℕ) := by
  have hle := ((pat_eq_self_iff p).1 hp).1
  have hlt : (p i.castSucc : ℕ) < n := lt_of_le_of_lt (hle i.castSucc) i.isLt
  simp only [restr, dif_pos hlt]



/-! ### How the block count changes -/


lemma image_extend_castSucc {q : Fin n → Fin n} {w : Fin n} (hw : w ∈ univ.image q) :
    univ.image (extend q w.castSucc) = (univ.image q).image Fin.castSucc := by
  obtain ⟨v, -, hv⟩ := Finset.mem_image.1 hw
  ext b
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
    · exact ⟨q i, ⟨i, rfl⟩, by rw [extend_castSucc]⟩
    · exact ⟨w, ⟨v, hv⟩, by rw [extend_last]⟩
  · rintro ⟨c, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.castSucc, by rw [extend_castSucc]⟩


lemma card_image_extend_castSucc {q : Fin n → Fin n} {w : Fin n} (hw : w ∈ univ.image q) :
    (univ.image (extend q w.castSucc)).card = (univ.image q).card := by
  rw [image_extend_castSucc hw, Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

/-! ### The Stirling recursion -/





/-! ### Base cases and the identification with `Nat.stirlingSecond` -/







open Geometry.KernelPatterns in
theorem solution(n k : ℕ) :
    ((patternsWith (n + 1) (k + 1)).filter fun p => ¬ p (Fin.last n) = Fin.last n).card
      = (k + 1) * (patternsWith n (k + 1)).card := by
  classical
  have hmem_iff : ∀ p : Fin (n + 1) → Fin (n + 1),
      p ∈ (patternsWith (n + 1) (k + 1)).filter (fun p => ¬ p (Fin.last n) = Fin.last n) ↔
        (pat p = p ∧ (univ.image p).card = k + 1) ∧ p (Fin.last n) ≠ Fin.last n := by
    intro p
    simp only [Finset.mem_filter, mem_patternsWith]
  -- the representative of the last index is not the last index, hence lies in `Fin n`
  have hlt : ∀ p : Fin (n + 1) → Fin (n + 1), p (Fin.last n) ≠ Fin.last n →
      ((p (Fin.last n) : ℕ)) < n := by
    intro p h2
    have h1 : (p (Fin.last n) : ℕ) ≤ n := Nat.lt_succ_iff.1 (p (Fin.last n)).isLt
    have h3 : (p (Fin.last n) : ℕ) ≠ n := fun h => h2 (Fin.ext (by simpa using h))
    omega
  have hlast_mem : ∀ p : Fin (n + 1) → Fin (n + 1), pat p = p →
      p (Fin.last n) ≠ Fin.last n →
      p (Fin.last n) ∈ (univ.image (restr p)).image Fin.castSucc := by
    intro p hpat h2
    have hidem := ((pat_eq_self_iff p).1 hpat).2
    refine Finset.mem_image.2 ⟨⟨(p (Fin.last n) : ℕ), hlt p h2⟩, ?_, ?_⟩
    · refine Finset.mem_image.2 ⟨⟨(p (Fin.last n) : ℕ), hlt p h2⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      have hcast : (⟨(p (Fin.last n) : ℕ), hlt p h2⟩ : Fin n).castSucc = p (Fin.last n) :=
        Fin.ext (by simp)
      rw [restr_apply_val hpat, hcast, hidem]
    · exact Fin.ext (by simp)
  have hmaps : ∀ p ∈ (patternsWith (n + 1) (k + 1)).filter
      (fun p => ¬ p (Fin.last n) = Fin.last n), restr p ∈ patternsWith n (k + 1) := by
    intro p hp
    obtain ⟨⟨hpat, hcard⟩, hlast⟩ := (hmem_iff p).1 hp
    refine (mem_patternsWith _).2 ⟨pat_restr hpat, ?_⟩
    obtain ⟨w, hw, hwcast⟩ := Finset.mem_image.1 (hlast_mem p hpat hlast)
    have hpe : extend (restr p) w.castSucc = p := by
      rw [hwcast]; exact extend_restr hpat
    have hcnt := card_image_extend_castSucc hw
    rw [hpe, hcard] at hcnt
    exact hcnt.symm
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ q ∈ patternsWith n (k + 1),
      (((patternsWith (n + 1) (k + 1)).filter fun p => ¬ p (Fin.last n) = Fin.last n).filter
        fun p => restr p = q).card = k + 1 := by
    intro q hq
    rw [mem_patternsWith] at hq
    obtain ⟨hqpat, hqcard⟩ := hq
    have hqidem := ((pat_eq_self_iff q).1 hqpat).2
    have hcard_img : ((univ.image q).image Fin.castSucc).card = k + 1 := by
      rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n), hqcard]
    refine Eq.trans ?_ hcard_img
    refine Finset.card_bij' (fun p _ => p (Fin.last n)) (fun a _ => extend q a) ?_ ?_ ?_ ?_
    · intro p hp
      obtain ⟨hpB, hpq⟩ := Finset.mem_filter.1 hp
      obtain ⟨⟨hpat, -⟩, hlast⟩ := (hmem_iff p).1 hpB
      have := hlast_mem p hpat hlast
      rwa [hpq] at this
    · intro a ha
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 ha
      have hqw : q w = w := by
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hw
        exact hqidem v
      refine Finset.mem_filter.2 ⟨(hmem_iff _).2 ⟨⟨pat_extend hqpat (Or.inr ⟨w, hqw, rfl⟩), ?_⟩, ?_⟩,
        restr_extend q w.castSucc⟩
      · rw [card_image_extend_castSucc hw, hqcard]
      · show extend q w.castSucc (Fin.last n) ≠ Fin.last n
        rw [extend_last]
        exact Fin.castSucc_ne_last w
    · intro p hp
      obtain ⟨hpB, hpq⟩ := Finset.mem_filter.1 hp
      obtain ⟨⟨hpat, -⟩, -⟩ := (hmem_iff p).1 hpB
      show extend q (p (Fin.last n)) = p
      rw [← hpq]
      exact extend_restr hpat
    · intro a _
      exact extend_last q a
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
