-- Prove2me | Definitions.Def_mme_recursive_x_hash_families
-- name    : mme_recursive_x_hash_families
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-11T22:43:19.565579+00:00
-- url     : https://prove2.me/theorems/422090bf-7d4f-4313-9da8-32758c9afc02
-- title:
--   Recursive joint-profile and marginal families with actual affine bucket filters
-- statement:
--   Fix a half-grade $h$, parent triples $p^{(r)}\in\mathbb N^3$, word lengths $n_r$, and prescribed integer joint histograms $m_r$. Put
--
--   $$C_r=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p^{(r)}_i\},\qquad W=\prod_r C_r^{n_r}.$$
--
--   Let $T\subseteq W$ contain the words whose joint histogram in each parent component is exactly $m_r$. Let $A\subseteq W$ contain all words whose three coordinate histograms in each component are the marginals of $m_r$. Thus $A$ includes potential competitors with other joint histograms. Write $X(w)$ for the full first-coordinate block and $N_X=|X(A)|$.
--
--   The module defines the componentwise recursive address space, the physical coordinate blocks, the exact target and full marginal-compatible ambient families, and the embedding of all positions into the finite affine hash domain. It records both common-label retention and independent coordinate-bucket filtering. No uniformity, collision bound, or existence of an isolated family is assumed. The support and histogram predicates reuse the existing recursive split definitions.
-- source:
--   Finite auxiliary formalization of the recursive hashing step in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6.2, Claim 6.6 and Lemma 6.7; https://arxiv.org/html/2404.16349v2#S6.SS2. The result isolates the finite counting and X-isolation argument. It does not assert the asymptotic Salem-Spencer set estimate or the full extraction theorem.

import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_dwz_asymmetric_affine_hash

open BigOperators MME.RecursiveThinSplit

set_option autoImplicit false

namespace MME.RecursiveXHash

/-- A recursive region has one word of admissible left-half splits per parent type. -/
abbrev Address (half R : ℕ) (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ) :=
  ∀ r, Fin (n r) → Split half (parent r)

/-- The physical coordinate block, kept separately within each parent type. -/
def block {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (i : Fin 3) (w : Address half R parent n) : ∀ r, Fin (n r) → Fin (half + 1) :=
  fun r t ↦ (w r t).val i

/-- All triples with the prescribed coordinate histograms, including competitors
whose joint profiles differ from the prescribed profiles. -/
noncomputable def ambient {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ) :
    Finset (Address half R parent n) := by
  classical
  exact Finset.univ.filter (fun w ↦ ∀ r, HasMarginalCounts (w r) (m r))

/-- The exact joint-profile triples sought inside the ambient family. -/
noncomputable def target {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ) :
    Finset (Address half R parent n) := by
  classical
  exact Finset.univ.filter (fun w ↦ ∀ r, HasJointCounts (w r) (m r))

/-- Flatten the region's positions and embed its physical grades in the prime field. -/
def fieldWord {half R N : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (p : ℕ) (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (i : Fin 3) (w : Address half R parent n) : Fin (N + 1) → ZMod p :=
  fun t ↦ ((block i w (e t).1 (e t).2).val : ZMod p)

/-- The full ambient family retained at common affine hash labels in S.
For an AP-free S this is exactly the independent three-coordinate bucket filter. -/
noncomputable def hashed {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (q : (Fin (N + 2) → ZMod p) × ZMod p) : Finset (Address half R parent n) := by
  classical
  exact (ambient m).filter (fun w ↦ dwzAsymmetricAffineRetains (half : ZMod p) S
    (fieldWord p e 0 w) (fieldWord p e 1 w) (fieldWord p e 2 w) q)

/-- Independent coordinate-bucket filtering, the actual first zeroing step. -/
noncomputable def bucketed {half R N p : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (q : (Fin (N + 2) → ZMod p) × ZMod p) : Finset (Address half R parent n) := by
  classical
  let ω := dwzAsymmetricHashStateOfAffine q
  exact (ambient m).filter (fun w ↦
    dwzAsymmetricHashX ω (fieldWord p e 0 w) ∈ S ∧
    dwzAsymmetricHashY ω (fieldWord p e 1 w) ∈ S ∧
    dwzAsymmetricHashZ (half : ZMod p) ω (fieldWord p e 2 w) ∈ S)

end MME.RecursiveXHash


