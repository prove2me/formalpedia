-- Prove2me | solution 1 for DepthDecay.probe_collision_of_depth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:28:23.160006+00:00
-- url     : https://prove2.me/submissions/20ace793-6a75-4683-94b5-238b6c334c82

-- Sol generated from Cryptography/DepthDecay/PathRealization.lean
import Mathlib
import Definitions.Def_Cryptography_DepthDecay_PathRealization
import Definitions.Def_Cryptography_DepthDecay_WindowSensor
import Theorems.Thm_DepthDecay_Adm_child
import Theorems.Thm_DepthDecay_letterAt_succ
import Theorems.Thm_DepthDecay_letterOf_child
import Theorems.Thm_DepthDecay_parent_child

/-!
# Realizing paths, and an entropy form of the depth decay

The first two files study the descent map `parent` and what a fixed-precision
magnitude probe can read off it.  Here we go the other way: we *build* states
from words, prove that the descent reads the word back letter by letter, and use
that to obtain a counting (pigeonhole) form of the depth decay which is
independent of the explicit straddling construction of
`Cryptography.DepthDecay.NullBeyondInversion`.

## Main results

* `Adm.child`, `letterOf_child`, `parent_child` : the three Berggren children are
  admissibility-preserving sections of the descent, and each child is tagged by
  its own letter.
* `letterAt_build` : the descent path of `build w` is the word `w`.  Every word
  is realized, so the tree really carries `3^k` distinct depth-`k` behaviours.
* `probe_mem_Ico` : on the stratum of states built from `{A,B}`-words the ratio
  stays in `(1,3)`, so a `W`-window probe takes at most `2·2^W` distinct values
  there.
* `probe_collision_of_depth` : **entropy form of the depth decay.**  Once
  `2·2^W < 2^k`, i.e. once the depth exceeds the window budget by two bits, the
  `W`-window sensor must confuse two admissible states whose paths differ at some
  depth below `k`.  The magnitude channel simply does not have the capacity to
  carry the deep letters.
-/

open DepthDecay



theorem adm_root : Adm root := by
  refine ⟨by norm_num [root], by norm_num [root], by norm_num [root], by norm_num [root]⟩




theorem adm_build : ∀ w : List Letter, Adm (build w)
  | [] => adm_root
  | x :: w => (adm_build w).child x

/-- **Every word is realized.**  The descent path of `build w` reads back `w`. -/
theorem letterAt_build : ∀ (w : List Letter) (j : ℕ) (hj : j < w.length),
    letterAt j (build w) = w[j] := by
  intro w
  induction w with
  | nil => intro j hj; simp at hj
  | cons x w ih =>
    intro j hj
    cases j with
    | zero => simpa [letterAt, build] using letterOf_child (adm_build w) x
    | succ j =>
      rw [letterAt_succ, build, parent_child (adm_build w) x]
      simpa using ih j (by simpa using hj)

/-! ### The bounded-ratio stratum -/

/-- Words over `{A,B}` keep the ratio below `3`. -/
theorem build_lt_three : ∀ w : List Letter, (∀ x ∈ w, x = Letter.A ∨ x = Letter.B) →
    (build w).1 < 3 * (build w).2
  | [], _ => by norm_num [build, root]
  | x :: w, hw => by
    have hAdm := adm_build w
    obtain ⟨hp, hlt, _, _⟩ := hAdm
    rcases hw x (by simp) with h | h <;> subst h
    · simp [build, DepthDecay.child]; omega
    · simp [build, DepthDecay.child]; omega

/-- On that stratum the `W`-window probe takes at most `2·2^W` values. -/
theorem probe_mem_Ico (W : ℕ) (w : List Letter) (hw : ∀ x ∈ w, x = Letter.A ∨ x = Letter.B) :
    probe W (build w) ∈ Finset.Ico (2 ^ W) (3 * 2 ^ W) := by
  have hAdm := adm_build w
  obtain ⟨hp, hlt, _, _⟩ := hAdm
  have h3 := build_lt_three w hw
  have hpow : 0 < 2 ^ W := Nat.two_pow_pos W
  refine Finset.mem_Ico.2 ⟨?_, ?_⟩
  · exact (Nat.le_div_iff_mul_le hp).2 (by nlinarith)
  · exact (Nat.div_lt_iff_lt_mul hp).2 (by nlinarith)


theorem boolWord_length {k : ℕ} (v : Fin k → Bool) : (boolWord v).length = k := by
  simp [boolWord]

theorem boolWord_mem {k : ℕ} (v : Fin k → Bool) :
    ∀ x ∈ boolWord v, x = Letter.A ∨ x = Letter.B := by
  intro x hx
  rw [boolWord, List.mem_ofFn] at hx
  obtain ⟨i, hi⟩ := hx
  by_cases hv : v i <;> simp [hv] at hi <;> simp [← hi]

theorem letterAt_boolWord {k : ℕ} (v : Fin k → Bool) (j : ℕ) (hj : j < k) :
    letterAt j (build (boolWord v)) = if v ⟨j, hj⟩ then Letter.A else Letter.B := by
  have hlen : j < (boolWord v).length := by simpa [boolWord_length] using hj
  rw [letterAt_build (boolWord v) j hlen]
  simp [boolWord]

/-! ### Entropy form of the depth decay -/



open DepthDecay in
theorem solution(W k : ℕ) (hk : 2 * 2 ^ W < 2 ^ k) :
    ∃ s s' : ℕ × ℕ, Adm s ∧ Adm s' ∧ probe W s = probe W s' ∧
      ∃ j < k, letterAt j s ≠ letterAt j s' := by
  classical
  have hcard : (Finset.Ico (2 ^ W) (3 * 2 ^ W)).card <
      (Finset.univ : Finset (Fin k → Bool)).card := by
    simp [Nat.card_Ico]
    omega
  obtain ⟨v, -, v', -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun v : Fin k → Bool => probe W (build (boolWord v)))
      (fun v _ => probe_mem_Ico W (boolWord v) (boolWord_mem v))
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  refine ⟨build (boolWord v), build (boolWord v'), adm_build _, adm_build _, heq, i, i.isLt, ?_⟩
  rw [letterAt_boolWord v i i.isLt, letterAt_boolWord v' i i.isLt]
  cases hv : v i <;> cases hv' : v' i <;> simp [hv, hv'] at hi ⊢
