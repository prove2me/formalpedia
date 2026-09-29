-- Prove2me | solution 1 for AlgebraicCodingTheory.card_zero_evaluations_le_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:10:22.430921+00:00
-- url     : https://prove2.me/submissions/7ad52994-736b-4977-8bef-e8fc670425f0

-- Sol generated from Cryptography/AlgebraicCodingTheory.lean
import Mathlib
import Definitions.Def_Cryptography_AlgebraicCodingTheory

/-!
# Reed–Solomon codes over finite fields

This file gives a direct polynomial-evaluation construction of Reed–Solomon codes and
proves their designed-distance bound.  It also derives injectivity, separation, and a
unique-decoding theorem from the bound.
-/

open AlgebraicCodingTheory

open Polynomial

variable {F : Type*} [Field F] [DecidableEq F]










open AlgebraicCodingTheory in
theorem solution{n : ℕ} (points : Fin n → F)
    (hpoints : Function.Injective points) (p : F[X]) (hp : p ≠ 0) :
    (Finset.univ.filter fun i => p.eval (points i) = 0).card ≤ p.natDegree := by
  have hroots : p.roots.card ≤ p.natDegree := by
    have := Polynomial.card_roots hp
    rw [Polynomial.degree_eq_natDegree hp] at this
    exact WithBot.coe_le_coe.mp this
  -- The filtered indices map via points to distinct roots
  have himage : ((Finset.univ.filter fun i => p.eval (points i) = 0).image points).card =
                (Finset.univ.filter fun i => p.eval (points i) = 0).card := by
    exact Finset.card_image_of_injective _ hpoints
  -- The image is a subset of roots
  have hsub : (Finset.univ.filter fun i => p.eval (points i) = 0).image points ⊆ p.roots.toFinset := by
    rw [Finset.image_subset_iff]
    intro i hi
    simp [Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact hi
  have htofinset : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le p.roots
  calc (Finset.univ.filter fun i => p.eval (points i) = 0).card
      = ((Finset.univ.filter fun i => p.eval (points i) = 0).image points).card := himage.symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := htofinset
    _ ≤ p.natDegree := hroots
