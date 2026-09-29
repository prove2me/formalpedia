-- Prove2me | solution 1 for PGLQuotient.sum_lam_sub_eq_pairExp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:27:34.778967+00:00
-- url     : https://prove2.me/submissions/c976103d-ba72-4081-abba-a33e51e9c21b

-- Sol generated from Algebra/PGLQuotient/VertexModel.lean
import Mathlib
import Definitions.Def_Algebra_PGLQuotient_VertexModel
import Theorems.Thm_PGLQuotient_lam_sub_indicator

/-!
# The standard arithmetic quotient of `PGL_d`: the vertex model

This file sets up an explicit combinatorial model for the vertex set of the standard
non-uniform arithmetic quotient of the affine Bruhat–Tits building of
`PGL_d (F_q((t^{-1})))` by `Γ = PGL_d(F_q[t])`.

By Soulé's theorem the quotient `Γ \ X` is (simplicially) a dominant sector: its vertices are
in bijection with dominant coweights `λ = (λ_0 ≥ λ_1 ≥ ⋯ ≥ λ_{d-1} = 0)`, and the stabiliser
of the vertex `λ` in `GL_d(F_q[t])` is the group of matrices `(a_{ij})` over `F_q[t]` with
`deg a_{ij} ≤ λ_i - λ_j`; equivalently, it is the automorphism group of the vector bundle
`⨁_i O(λ_i)` on `P^1`, i.e. the unit group of the algebra `End = ⨁_{i,j} H^0(O(λ_i - λ_j))`.
Its order is

`|Aut(λ)| = q^{dim End} * ∏_i (1 - q^{-r_i})`,

where `dim End = ∑_{i,j} max (0, λ_i - λ_j + 1)` and `r_i = #{ j ≤ i : λ_j = λ_i }` is the
position of `i` inside its block of equal entries (so that the second factor accounts for the
Levi `∏_b GL_{m_b}(F_q)` of the block composition).  With the Haar measure normalised so that
a maximal compact subgroup has volume `1`, the vertex `λ` carries the mass `1/|Aut(λ)|`
(`GL`-normalisation) resp. `(q-1)/|Aut(λ)|` (`PGL`-normalisation).

Vertices are parametrised here by their *gaps* `g_k = λ_k - λ_{k+1} ∈ ℕ`, `0 ≤ k ≤ d-2`, i.e.
by `Vertex d = Fin (d-1) → ℕ`.

The homothety-invariant normalised lattice-minima height is
`α(λ) = q^{λ_0 - (λ_0 + ⋯ + λ_{d-1})/d}`, which in gap coordinates reads
`log_q α = (∑_k (d-1-k) g_k)/d`.

## Main results of this file

* `sum_lam_sub_eq_pairExp` : the cut-set/double-counting identity
  `∑_{i,j} (λ_i - λ_j) = ∑_k (k+1)(d-1-k) g_k`;
* `vertexWeight_le`, `vertexWeight_ge` : sharp-order two-sided bounds
  `c₁ q^{-P(g)} ≤ 1/|Aut(λ)| ≤ c₂ q^{-P(g)}` with `P(g) = ∑_k (k+1)(d-1-k) g_k`.

These drive all the analytic results (integrability threshold, cusp tail, height zeta
function) in the companion files.
-/

open PGLQuotient

open Finset


variable {d : ℕ}












variable (g : Vertex d)











variable {q : ℝ} (g : Vertex d)














open PGLQuotient in
theorem solution:
    ∑ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j) = pairExp g := by
  have h1 : ∀ i ∈ range d, ∑ j ∈ range d, (lam g i - lam g j)
      = ∑ j ∈ range d, ∑ k ∈ range (d-1), (if i ≤ k ∧ k < j then gapAt g k else 0) := by
    intro i _
    exact Finset.sum_congr rfl (fun j hj => lam_sub_indicator g (Finset.mem_range.mp hj))
  rw [Finset.sum_congr rfl h1]
  have step1 : ∀ i : ℕ, ∑ j ∈ range d, ∑ k ∈ range (d-1), (if i ≤ k ∧ k < j then gapAt g k else 0)
      = ∑ k ∈ range (d-1), ∑ j ∈ range d, (if i ≤ k ∧ k < j then gapAt g k else 0) :=
    fun i => Finset.sum_comm
  rw [Finset.sum_congr rfl (fun i _ => step1 i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkd : k < d - 1 := Finset.mem_range.mp hk
  have inner : ∀ i : ℕ, ∑ j ∈ range d, (if i ≤ k ∧ k < j then gapAt g k else 0)
      = if i ≤ k then (d - 1 - k) * gapAt g k else 0 := by
    intro i
    by_cases hik : i ≤ k
    · simp only [hik, true_and, if_true]
      rw [← Finset.sum_filter]
      have hfil : (range d).filter (fun j => k < j) = Finset.Ico (k+1) d := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      rw [hfil, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      congr 1
      omega
    · simp [hik]
  rw [Finset.sum_congr rfl (fun i _ => inner i), ← Finset.sum_filter]
  have hfil2 : (range d).filter (fun i => i ≤ k) = range (k+1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfil2, Finset.sum_const, Finset.card_range, smul_eq_mul, ← mul_assoc]
