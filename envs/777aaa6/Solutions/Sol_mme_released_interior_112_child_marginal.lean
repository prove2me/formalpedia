-- Prove2me | solution 1 for mme_released_interior_112_child_marginal
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:50:49.834883+00:00
-- url     : https://prove2.me/submissions/07ec106b-f363-4fa9-9854-2615b5c4e2eb

import Definitions.Def_mme_released_interior_integer_profiles
open MME MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

private def outerCount (t : Term) (j : ℕ) (z : Fin 3) : ℕ :=
  ((t.children.find? (fun c => c.1 == j && c.2.1 ==
    List.ofFn (fun i : Fin 3 => if i = z then 2 else 1))).getD (0, [], 0)).2.2

private theorem child112_atom_list (t : Term) (j : ℕ) (z : Fin 3) :
    child t j (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1)) =
      (childSupport (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1))).map
        (fun a => (a, if (childWord 0 a z) = ![0, 2] ∨ (childWord 0 a z) = ![2, 0]
          then outerCount t j z else denominator / 2 - outerCount t j z)) := by
  fin_cases z <;> rfl

private theorem support_112 (z : Fin 3) :
    childSupport (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1)) =
      ![[11, 22, 27, 31], [10, 15, 20, 25], [4, 9, 19, 24]] z := by
  fin_cases z <;> decide +kernel

private theorem weighted_count_sum {A : Type*} (l : List A)
    (test outer : A → Bool) (p q : ℕ) :
    (l.map (fun a => if test a then (if outer a then p else q) else 0)).sum =
      (l.filter (fun a => test a && outer a)).length * p +
        (l.filter (fun a => test a && !outer a)).length * q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases ht : test a <;> cases ho : outer a <;>
      simp [ht, ho, ih, Nat.add_mul] <;> omega

private theorem marginal_counts : ∀ (z i : Fin 3) (w : CompleteWord 2),
    let support := childSupport (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1))
    let test := fun a => decide (childWord 0 a i = w)
    let outer := fun a => decide (childWord 0 a z = ![0, 2] ∨ childWord 0 a z = ![2, 0])
    ((support.filter (fun a => test a && outer a)).length =
      if i = z then (if w = ![0, 2] ∨ w = ![2, 0] then 1 else 0)
      else (if w = ![0, 1] ∨ w = ![1, 0] then 1 else 0)) ∧
    ((support.filter (fun a => test a && !outer a)).length =
      if i = z then (if w = ![1, 1] then 2 else 0)
      else (if w = ![0, 1] ∨ w = ![1, 0] then 1 else 0)) := by
  decide +kernel

private theorem parametric_marginal (p : ℕ) (hp : p ≤ denominator / 2)
    (z i : Fin 3) (w : CompleteWord 2) :
    ((childSupport (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1))).map
      (fun a => if childWord 0 a i = w then
        (if childWord 0 a z = ![0, 2] ∨ childWord 0 a z = ![2, 0]
          then p else denominator / 2 - p) else 0)).sum =
      if i = z then
        if w = ![0, 2] ∨ w = ![2, 0] then p
        else if w = ![1, 1] then denominator - 2 * p else 0
      else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0  := by
  have h := weighted_count_sum
    (childSupport (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1)))
    (fun a => decide (childWord 0 a i = w))
    (fun a => decide (childWord 0 a z = ![0, 2] ∨ childWord 0 a z = ![2, 0]))
    p (denominator / 2 - p)
  simp only [decide_eq_true_eq] at h
  rw [h, (marginal_counts z i w).1, (marginal_counts z i w).2]
  by_cases hiz : i = z
  · by_cases ho : w = ![0, 2] ∨ w = ![2, 0]
    · have hm : w ≠ ![1, 1] := by
        rcases ho with rfl | rfl <;> decide
      simp [hiz, ho, hm]
    · by_cases hm : w = ![1, 1]
      · simp only [if_pos hiz, if_neg ho, if_pos hm, zero_mul, zero_add]
        norm_num [denominator] at hp ⊢
        omega
      · simp [hiz, ho, hm]
  · by_cases hw : w = ![0, 1] ∨ w = ![1, 0]
    · simp only [if_neg hiz, if_pos hw, one_mul]
      omega
    · simp [hiz, hw]


private theorem role_zero : ∀ i : Fin 3, role 0 i = i := by decide +kernel
private theorem role_injective : ∀ owner : Fin 6, Function.Injective (role owner) := by
  decide +kernel
private theorem child_word_role (owner : Fin 6) (a : ℕ) (i : Fin 3) :
    childWord owner a i = childWord 0 a (role owner i) := by
  funext h
  simp only [childWord, role_zero]

private theorem source_shape_112 (owner : Fin 6) {s : Fin 45}
    (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    sourceShape owner c = List.ofFn (fun i : Fin 3 => if i = role owner z then 2 else 1) := by
  unfold sourceShape
  congr 1
  funext i
  rw [hshape]
  have heq : inverseRole owner i = z ↔ i = role owner z := by
    fin_cases owner <;> fin_cases z <;> fin_cases i <;> decide
  simp only [heq]



private theorem child112_marginal (t : Term) (j : ℕ) (z i : Fin 3)
    (w : CompleteWord 2) (hp : outerCount t j z ≤ denominator / 2) :
    ((child t j (List.ofFn (fun i : Fin 3 => if i = z then 2 else 1))).map
      (fun a => if childWord 0 a.1 i = w then a.2 else 0)).sum =
      if i = z then
        if w = ![0, 2] ∨ w = ![2, 0] then outerCount t j z
        else if w = ![1, 1] then denominator - 2 * outerCount t j z else 0
      else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 := by
  rw [child112_atom_list]
  simpa only [List.map_map, Function.comp_def] using
    parametric_marginal (outerCount t j z) hp z i w

/-- The released square-child marginals have the canonical 112 formula in
any coordinate placement, after applying the owner's actual role permutation.
The parameter bound is retained explicitly for natural-number subtraction. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let p := (((seed owner s).children.find?
      (fun a => a.1 == r.val && a.2.1 == sourceShape owner c)).getD (0, [], 0)).2.2
    p ≤ denominator / 2 → ∀ (i : Fin 3) (w : CompleteWord 2),
      childMarginal owner s r c i w =
        if i = z then
          if w = ![0, 2] ∨ w = ![2, 0] then p
          else if w = ![1, 1] then denominator - 2 * p else 0
        else if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0 := by
  dsimp only
  intro hp i w
  unfold childMarginal
  rw [source_shape_112 owner c z hshape]
  have hp' : outerCount (seed owner s) r.val (role owner z) ≤ denominator / 2 := by
    simpa only [outerCount, source_shape_112 owner c z hshape] using hp
  have h := child112_marginal (seed owner s) r.val (role owner z) (role owner i) w hp'
  simpa only [outerCount, (role_injective owner).eq_iff, ← child_word_role owner] using h


#print axioms solution
