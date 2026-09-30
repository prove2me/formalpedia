-- Prove2me | Theorems.Thm_Hirsch_spindle_normalize
-- name    : Hirsch.spindle_normalize
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T15:01:24.888233+00:00
-- url     : https://prove2.me/theorems/74af7713-0235-4065-85e4-33bcfc6a6a77
-- title:
--   Normalise a spindle so the apices are $\pm e_d$
-- statement:
--   A spindle can be affinely moved so that its apices are $e_d$ and $-e_d$.
--
--   Let $P\subseteq\mathbb R^d$ ($d>0$) be a nonempty bounded H-polytope which is a spindle of length greater than $d$ with apices $u,v$. Then there exist inequalities describing an H-polytope $P'$ and an affine automorphism of $\mathbb R^d$ carrying $P$ onto $P'$, sending $u$ to the last standard basis vector $e_d$ and $v$ to $-e_d$.
--
--   The image $P'$ is nonempty and bounded, $e_d$ and $-e_d$ are extreme, every describing inequality of $P'$ is tight at exactly one of them, tightness of the original $i$-th inequality at $u$ matches tightness of the $i$-th inequality of $P'$ at $e_d$, and there is no padded vertex-edge walk of length $d$ from $e_d$ to $-e_d$.
--
--   This normalisation is the standard first step before writing Santos' one-point-suspension in coordinates aligned with the apices.
--
--   **Formalization Note.** The last basis vector is `EuclideanSpace.single ⟨d-1, _⟩ 1`.
-- source:
--   F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, https://arxiv.org/abs/1006.2814, Section 2.2 (coordinates with distinguished apices before the one-point-suspension).

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

/-- A spindle can be affinely moved so that its apices are $e_d$ and $-e_d$.

Let $P\subseteq\mathbb R^d$ be a nonempty bounded H-polytope that is a spindle
of length greater than $d$ with apices $u,v$. Then there is an affine
automorphism of $\mathbb R^d$ carrying $P$ to another such H-polytope $P'$
whose apices are the last standard basis vector and its negative, preserving
nonemptiness, boundedness, the spindle (XOR) property, and the absence of a
padded walk of length $d$ between the apices. -/
theorem spindle_normalize (d n : ℕ) (hd : 0 < d)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hne : (Hpoly a b).Nonempty) (hbd : Bornology.IsBounded (Hpoly a b))
    (hu : u ∈ Set.extremePoints ℝ (Hpoly a b))
    (hv : v ∈ Set.extremePoints ℝ (Hpoly a b))
    (hspindle : ∀ i, (⟪a i, u⟫ = b i) ↔ ⟪a i, v⟫ ≠ b i)
    (hlong : ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
      ¬ (w 0 = u ∧ w d = v ∧
          ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)))) :
    ∃ (a' : Fin n → EuclideanSpace ℝ (Fin d)) (b' : Fin n → ℝ),
      (Hpoly a' b').Nonempty ∧
      Bornology.IsBounded (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∈
        Set.extremePoints ℝ (Hpoly a' b') ∧
      (∀ i, (⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ)⟫ ≠ b' i) ∧
      (∀ i, ⟪a i, u⟫ = b i ↔
        ⟪a' i, EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ)⟫ = b' i) ∧
      ∀ w : ℕ → EuclideanSpace ℝ (Fin d),
        ¬ (w 0 = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (1 : ℝ) ∧
            w d = EuclideanSpace.single ⟨d - 1, Nat.sub_lt hd (by decide)⟩ (-1 : ℝ) ∧
            ∀ j < d, w j = w (j + 1) ∨ Adj (Hpoly a' b') (w j) (w (j + 1))) := by sorry

end Hirsch
