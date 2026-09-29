-- Prove2me | Theorems.Thm_mme_dwz_table2_affine_hash_incidence_factory
-- name    : mme_dwz_table2_affine_hash_incidence_factory
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T05:37:50.271355+00:00
-- url     : https://prove2.me/theorems/073c1912-0f06-47cc-a9f9-23aaa1cf92b0
-- title:
--   Exact affine incidences for literal Table-2 block pruning
-- statement:
--   For any finite ambient and target families of length-$N+1$ Table-2 component words, with the target contained in the ambient family, fix an odd prime $p\geq5$ and a three-term-progression-free set $S\subseteq[0,p/2)$. Literal affine block pruning produces a surviving-family function over exactly $p^{N+3}$ states such that every target word occurs in exactly $|S|p^{N+1}$ states, while every directed distinct pair sharing its $X$ or $Y$ projection occurs together in at most $|S|p^N$ states. These are precisely the finite incidence inputs to the first asymmetric-hashing retention theorem.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10 and Table 2.

import Definitions.Def_mme_dwz_square_data
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

set_option autoImplicit false

theorem mme_dwz_table2_affine_hash_incidence_factory
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ MME.DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    Fintype.card Ω = p ^ (N + 3) ∧
      ∃ E : Ω → Finset Edge,
        (∀ q, E q ⊆ A) ∧
        (∀ a ∈ T,
          (Finset.univ.filter (fun q : Ω ↦ a ∈ E q)).card =
            S.card * p ^ (N + 1)) ∧
        ∀ ab ∈ (T.product A).filter (fun ab ↦
            ab.1 ≠ ab.2 ∧ (x ab.1 = x ab.2 ∨ y ab.1 = y ab.2)),
          (Finset.univ.filter (fun q : Ω ↦
            ab.1 ∈ E q ∧ ab.2 ∈ E q)).card ≤
              S.card * p ^ N := by
  sorry
