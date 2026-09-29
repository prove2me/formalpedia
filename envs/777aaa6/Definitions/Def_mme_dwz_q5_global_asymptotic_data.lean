-- Prove2me | Definitions.Def_mme_dwz_q5_global_asymptotic_data
-- name    : mme_dwz_q5_global_asymptotic_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-18T13:35:54.089814+00:00
-- url     : https://prove2.me/theorems/e408b88f-7b5e-456f-8664-202c78ada31c
-- title:
--   Exact q=5 global count sequences and extraction-rate expressions
-- statement:
--   This records the exact finite counts and their entropy rates for the original rational-replay $q=5$ fourth-power candidate. The 45 parent Z profiles and outer weights are unchanged.
--
--   For a positive integer scaling parameter $t$, let $D$ be the product of the profile denominators, $m_c=a_cDt/d_c$, $n_c=d_cm_c$ and $N=\sum_c n_c$. The ambient degree is the full sum of fixed-coordinate multinomial weights over every supported joint table with the three prescribed marginals. The target count is $T=N!/\prod_c n_c!$. The compatibility count $W$ is the boundary/pooled two-stage factorial formula for the original profiles, including the owner. These are the same quantities in the exact global counting and numerical-budget extraction theorems.
--
--   For the integral seed at $t=1$, write $F_i$ for each aggregate fine-Z count, $q_{d,i}$ for each boundary or pooled interior class count, and $A_d=\sum_iq_{d,i}$. Define the rates in natural logarithms by
--   $$
--   H_T=\frac{N\log N-\sum_c n_c\log n_c}{N},\qquad
--   L_W=\frac{\sum_i F_i\log F_i-\sum_{d,i}q_{d,i}\log q_{d,i}+\sum_d A_d\log A_d-\sum_c n_c\log n_c}{N}.
--   $$
--   The marginal entropies are computed from the exact public marginal numerators divided by their common scale. With the public full-polytope entropy ceiling $U$, define
--   $$
--   L=\max\{0,U-H_X,U-H_Y,L_W\},\qquad R=H_T-L.
--   $$
--   This is pure notation for the finite counts and candidate extraction rate. It does not assert an asymptotic limit, an entropy bound, a tensor restriction or a positive surplus; those are separate theorems.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5, Section 6.2, Lemma 6.7, equations (22)-(24), and the modulus and retained-copy calculations; notation for the exact rational-replay candidate in the public q=5 global counting theorem.

import Definitions.Def_mme_dwz_q5_exact_global_profile_data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Pi

open BigOperators MME.DWZQ5ExactData MME.DWZFourthGlobalWitness
open scoped Classical
set_option autoImplicit false

namespace MME.DWZQ5AsymptoticData

noncomputable section

def D : ℕ := ∏ c : Fin 45, (rawProfile c).denominator

def m (t : ℕ) (c : Fin 45) : ℕ :=
  component c * (D * t) / (rawProfile c).denominator

def n (t : ℕ) (c : Fin 45) : ℕ := (rawProfile c).length (m t c)

def N (t : ℕ) : ℕ := ∑ c : Fin 45, n t c

def shape (c : Fin 45) (i : Fin 3) : ℕ := (coarseAddress c i).val

def z (t : ℕ) (c : Fin 45) (l : Fin 5) : ℕ :=
  (rawProfile c).count l * m t c

def mu (t : ℕ) : Fin 3 → Fin 45 → Fin 5 → ℕ
  | 0, c, l => if shape c 1 = 0 then z t c (Fin.rev l) else 0
  | 1, c, l => if shape c 0 = 0 then z t c (Fin.rev l) else 0
  | 2, c, l => z t c l

def M (t : ℕ) (i : Fin 3) (g : ℕ) : ℕ :=
  ∑ c : {c : Fin 45 // shape c i = g}, n t c.val

abbrev Cell := {s : Fin 3 → Fin 9 // (∑ i, (s i).val) = 8}

def tables (t : ℕ) : Finset (Cell → Fin (N t + 1)) :=
  Finset.univ.filter (fun h ↦ ∀ i : Fin 3, ∀ g : Fin 9,
    (∑ s : {s : Cell // s.val i = g}, (h s.val).val) = M t i g.val)

def degree (t : ℕ) (mode : Fin 3) : ℕ :=
  ∑ h ∈ tables t, ∏ g : Fin 9, (M t mode g.val).factorial /
    ∏ s : {s : Cell // s.val mode = g}, ((h s.val).val).factorial

def coarse (c : Fin 45) : Fin 9 := coarseAddress c 2

def boundary (c : Fin 45) : Prop := shape c 0 = 0 ∨ shape c 1 = 0

def F (t : ℕ) (i : Fin 9 × Fin 5) : ℕ :=
  ∑ c : {c : Fin 45 // coarse c = i.1}, mu t 2 c.val i.2

def pooled (t : ℕ) : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) → ℕ
  | (Sum.inl c, (g,l)) => if boundary c ∧ coarse c = g then mu t 2 c l else 0
  | (Sum.inr g', (g,l)) => if g' = g then F t (g,l) -
      ∑ c ∈ Finset.univ.filter (fun c ↦ boundary c ∧ coarse c = g), mu t 2 c l
    else 0

def collapse (c : Fin 45) : Fin 45 ⊕ Fin 9 :=
  if boundary c then Sum.inl c else Sum.inr (coarse c)

def W (t : ℕ) : ℕ :=
  (∏ i : Fin 9 × Fin 5, (F t i).factorial /
    ∏ di : {di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5) // di.2 = i},
      (pooled t di.val).factorial) *
  (∏ d : Fin 45 ⊕ Fin 9, (∑ i, pooled t (d,i)).factorial /
    ∏ c : {c : Fin 45 // collapse c = d}, (n t c.val).factorial)

def targetCount (t : ℕ) : ℕ := (N t).factorial / ∏ c, (n t c).factorial

def targetRate : ℝ :=
  ((N 1 : ℝ) * Real.log (N 1 : ℝ) -
    ∑ c, (n 1 c : ℝ) * Real.log (n 1 c : ℝ)) / (N 1 : ℝ)

def marginalEntropy (mode : Fin 3) : ℝ :=
  ∑ g : Fin 9, Real.negMulLog ((marginal mode g : ℝ) / (scale : ℝ))

def compatibilityRate : ℝ :=
  ((∑ i : Fin 9 × Fin 5, (F 1 i : ℝ) * Real.log (F 1 i : ℝ)) -
    (∑ di : (Fin 45 ⊕ Fin 9) × (Fin 9 × Fin 5),
      (pooled 1 di : ℝ) * Real.log (pooled 1 di : ℝ)) +
    (∑ d : Fin 45 ⊕ Fin 9,
      (∑ i, pooled 1 (d,i) : ℝ) * Real.log (∑ i, pooled 1 (d,i) : ℝ)) -
    (∑ c : Fin 45, (n 1 c : ℝ) * Real.log (n 1 c : ℝ))) / (N 1 : ℝ)

def hashRate : ℝ :=
  max 0 (max ((entropyUpper : ℝ) - marginalEntropy 0)
    (max ((entropyUpper : ℝ) - marginalEntropy 1) compatibilityRate))

def extractionRate : ℝ := targetRate - hashRate

end
end MME.DWZQ5AsymptoticData


