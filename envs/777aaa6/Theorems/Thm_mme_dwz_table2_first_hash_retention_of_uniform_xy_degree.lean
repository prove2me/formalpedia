-- Prove2me | Theorems.Thm_mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
-- name    : mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:48:41.345612+00:00
-- url     : https://prove2.me/theorems/f09b3b28-aa5d-496d-836b-4b6537ef9423
-- title:
--   Finite Table-2 first-hash retention from a uniform X/Y degree bound
-- statement:
--   Let $A$ be an ambient family of length-$N+1$ Table-2 component words and $T\subseteq A$ a target family. Suppose every target word has at most $d$ ambient competitors sharing its $X$ projection, and at most $d$ sharing its $Y$ projection. For an odd prime $p\geq5$ with $4d\leq p$ and a lower-half Salem–Spencer set $S$, literal affine pruning has a state whose surviving family contains an X/Y-induced target subfamily $I$ satisfying
--
--   $$|I|\geq |T||S|/(2p^2).$$
--
--   This is the finite first asymmetric-hashing conclusion used in Equation (21).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10 and Equation (21).

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false

theorem mme_dwz_table2_first_hash_retention_of_uniform_xy_degree
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A)
    (d : ℕ) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeX (b t)) =
          (fun t ↦ MME.DWZSquare.shapeX (a t)))).card ≤ d)
    (hy : ∀ a ∈ T,
      (A.filter (fun b ↦
        (fun t ↦ MME.DWZSquare.shapeY (b t)) =
          (fun t ↦ MME.DWZSquare.shapeY (a t)))).card ≤ d) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    ∃ E : Ω → Finset Edge,
      (∀ q, E q ⊆ A) ∧
      ∃ q : Ω, ∃ I : Finset Edge,
        I ⊆ T ∧
        I ⊆ E q ∧
        (∀ e ∈ I, ∀ e' ∈ E q,
          x e = x e' ∨ y e = y e' → e = e') ∧
        ((T.card : ℝ) * (S.card : ℝ)) /
            (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  sorry
