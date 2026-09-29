-- Prove2me | solution 1 for ClassGroupResidueDial.four_dvd_boxP_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:11:39.270595+00:00
-- url     : https://prove2.me/submissions/96ae14c0-9abd-44b7-b48e-da8b3fee3e5a

-- Sol generated from Algebra/ClassGroupResidueDial.lean
import Mathlib
import Definitions.Def_Algebra_ClassGroupResidueDial
import Theorems.Thm_ClassGroupResidueDial_card_eq_two_mul_of_involutive
/-
# The Extrinsic Class-Group Representation Vector is a Residue Dial

Formal core of the *factor3* investigation
`ResearchOutput/NewMathematics/35_ClassGroup_ResidueDial.md`
(experiment RANDOM-BQF #370).

## The question

Attach to an integer `N` an *extrinsic* discriminant `D` (independent of `N`),
form the finitely many reduced binary quadratic forms `Q_1, … , Q_h` of
discriminant `D`, and record the **representation vector**

  `r(N) = ( #{(x,y) : Q_1(x,y) = N}, … , #{(x,y) : Q_h(x,y) = N} )`.

Computing this vector is cheap (`poly(|D|, log N)`, no factoring).  The hope of
the round-13 brainstorm was that the individual entries feel the *separate*
Legendre symbols `(D/p)`, `(D/q)` of the factors of `N = p q`, so that the
vector could distinguish factorisation *types* which have the same residue
`N mod |D|`.

## What is proved here (`D = -20`, `h = 2`)

The two reduced forms of discriminant `-20` are

  `P(x,y) = x² + 5y²`   and   `Q(x,y) = 2x² + 2xy + 3y²`.

* `ClassGroupResidueDial.sound20` : a value of `P` coprime to `20` is `≡ 1, 9 (mod 20)`;
  a value of `Q` coprime to `20` is `≡ 3, 7 (mod 20)`  (finite check in `ZMod 20`).
* `ClassGroupResidueDial.ResidueDial.readout_eq` : consequently the *index of the class that
  represents `N`* is a **function of `N mod 20` alone** — the "residue dial".
* `ClassGroupResidueDial.comp20` : Gauss composition, realised by explicit bilinear
  identities: the two classes form the group `ℤ/2` under multiplication of
  represented integers (`P·P = P`, `Q·Q = P`, `P·Q = Q`).
* `ClassGroupResidueDial.obs_pp_eq_obs_nn` : **the refutation.**  If `p, q` are both
  represented by the principal form and `p', q'` are both represented by the
  non-principal form, then `pq` and `p'q'` have *identical* observation vectors
  `(true, false)`.  The "PP" and "NN" factorisation types are invisible.
* Exact counts (`reps_21_ncard`, `reps_87_ncard`, `reps_1189_ncard`) confirm the
  numerical `(8,0)` signature of the experiment on both a PP and an NN semiprime.

The abstract notion `ResidueDial` isolates exactly what makes the collapse
happen: *soundness* (each class only represents certain residues) plus
*disjointness* of those residue sets.  Any such family is factor-blind.
-/

open ClassGroupResidueDial

/-! ## 1. Abstract residue dials -/


variable {m : ℕ} {ι : Type*}






/-! ## 2. The discriminant `-20` dial -/










/-! ## 3. Consequences for `D = -20`: exclusivity and the dial -/






/-! ## 4. Gauss composition: the class group is `ℤ/2` -/





/-! ## 5. The refutation: PP and NN semiprimes are indistinguishable -/









/-! ## 6. Why the collision is unavoidable: the dial is a quadratic character -/







/-! ## 7. Lab notes: exact representation counts

The experiment reported the signature `(8, 0)` for semiprimes `N ≡ 1, 9 (mod 20)`
whose prime factors are split, *independently of the PP/NN type*.  Here are three
certified instances:

| `N`    | factorisation | type | `r_P(N)` | `r_Q(N)` |
|--------|---------------|------|----------|----------|
| `21`   | `3 · 7`       | NN   | `8`      | `0`      |
| `1189` | `29 · 41`     | PP   | `8`      | `0`      |
| `87`   | `3 · 29`      | PN   | `0`      | `8`      |
-/














open ClassGroupResidueDial in
theorem solution{N : ℤ} (hN : IsCoprime N 20) (hsq : ∀ k : ℤ, k ^ 2 ≠ N)
    (Bx By : ℤ) : 4 ∣ (boxP N Bx By).card := by
  classical
  have hmem : ∀ p ∈ boxP N Bx By, (-Bx ≤ p.1 ∧ p.1 ≤ Bx) ∧ (-By ≤ p.2 ∧ p.2 ≤ By) ∧
      p.1 ^ 2 + 5 * p.2 ^ 2 = N := by
    intro p hp
    simp only [boxP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hne : ∀ p ∈ boxP N Bx By, p.1 ≠ 0 ∧ p.2 ≠ 0 := by
    intro p hp
    obtain ⟨-, -, heq⟩ := hmem p hp
    constructor
    · rintro h0
      obtain ⟨a, b, hab⟩ := hN
      have h5 : (5 : ℤ) ∣ N := ⟨p.2 ^ 2, by rw [← heq, h0]; ring⟩
      have h1 : (5 : ℤ) ∣ 1 := by
        rw [← hab]
        exact dvd_add (Dvd.dvd.mul_left h5 a) ⟨4 * b, by ring⟩
      norm_num at h1
    · rintro h0
      exact hsq p.1 (by rw [← heq, h0]; ring)
  set S := boxP N Bx By with hS
  have h1 : S.card = 2 * (S.filter (fun p => 0 < p.1)).card := by
    refine card_eq_two_mul_of_involutive (fun p => (-p.1, p.2)) (by intro p; simp) ?_ _ ?_
    · intro p hp
      obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, heq⟩ := hmem p hp
      simp only [hS, boxP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by rw [← heq]; ring⟩
    · intro p hp
      have := (hne p hp).1
      simp only
      omega
  have h2 : (S.filter (fun p => 0 < p.1)).card
      = 2 * ((S.filter (fun p => 0 < p.1)).filter (fun p => 0 < p.2)).card := by
    refine card_eq_two_mul_of_involutive (fun p => (p.1, -p.2)) (by intro p; simp) ?_ _ ?_
    · intro p hp
      simp only [Finset.mem_filter] at hp ⊢
      obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, heq⟩ := hmem p hp.1
      refine ⟨?_, hp.2⟩
      simp only [hS, boxP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, by rw [← heq]; ring⟩
    · intro p hp
      have := (hne p (Finset.mem_filter.mp hp).1).2
      simp only
      omega
  omega
