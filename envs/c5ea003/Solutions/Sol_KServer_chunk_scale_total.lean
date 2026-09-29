-- Prove2me | solution 1 for KServer.chunk_scale_total
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T11:18:42.485117+00:00
-- url     : https://prove2.me/submissions/cce5d794-f59d-4e90-8a3d-f8b3aae6726f

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond

namespace KServer

namespace ScaleTotal

variable {X : Type*} [MetricSpace X]

/-- The partial cost of an evader on a chunk is nonnegative. -/
theorem costOn_nonneg (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    0 ≤ E.costOn h χ := by
  unfold EvaderAlgorithm.costOn EvaderAlgorithm.cost
  have hlen : (h ++ χ).length = h.length + χ.length := by simp
  have hsub : Finset.range h.length ⊆ Finset.range (h ++ χ).length := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hcongr : ∀ j ∈ Finset.range h.length,
      dist (E.pos ((h ++ χ).take j)) (E.pos ((h ++ χ).take (j + 1)))
        = dist (E.pos (h.take j)) (E.pos (h.take (j + 1))) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    rw [List.take_append_of_le_length (by omega),
      List.take_append_of_le_length (by omega)]
  have hsplit := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun j => dist (E.pos ((h ++ χ).take j)) (E.pos ((h ++ χ).take (j + 1))))
    (fun j _ _ => dist_nonneg)
  rw [Finset.sum_congr rfl hcongr] at hsplit
  linarith

/-- The cost of an evader on a chunk under an online escape rule with a
nonnegative escape price is nonnegative. -/
theorem bailCost_nonneg (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (h χ : List (Set X)) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ E.bailCost bail h χ p := by
  unfold EvaderAlgorithm.bailCost
  rcases hq : bailTime bail h χ with - | q
  · exact costOn_nonneg E h χ
  · have := costOn_nonneg E h (χ.take q)
    linarith

variable {s t : X} {cB T pe : ℝ} {mL : ℕ}

/-- The chunk system obtained by scaling every size by `lam ∈ [0,1]`. -/
noncomputable def scaled (C : ChunkSystemB X s t 0 cB T pe mL) (lam T' : ℝ)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hpe : 0 ≤ pe)
    (hT' : T' ≤ ∑ ω, C.P ω * ∑ i, lam * C.size ω i) :
    ChunkSystemB X s t 0 cB T' pe mL where
  Ω := C.Ω
  instFin := C.instFin
  instDec := C.instDec
  P := C.P
  m := C.m
  hist := C.hist
  chunk := C.chunk
  size := fun ω i => lam * C.size ω i
  hP := C.hP
  hPsum := C.hPsum
  hm := C.hm
  hm0 := C.hm0
  href := C.href
  hadapt := C.hadapt
  hsmeas := fun i ω ω' h => by rw [C.hsmeas i ω ω' h]
  hne := C.hne
  hlast := C.hlast
  hopt := C.hopt
  hsize := fun ω i => by
    refine ⟨mul_nonneg hlam0 (C.hsize ω i).1, ?_⟩
    have h1 := (C.hsize ω i).1
    have h2 := (C.hsize ω i).2
    nlinarith
  hcost := by
    intro i ω₀ E bail
    have horig := C.hcost i ω₀ E bail
    have hmul : lam * (C.size ω₀ i
        * (∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀), C.P ω))
        ≤ lam * (∑ ω ∈ Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀),
          C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten)
            (C.chunk ω i) pe) :=
      mul_le_mul_of_nonneg_left horig hlam0
    refine le_trans (le_of_eq (by ring)) (le_trans hmul ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hb := bailCost_nonneg E bail (((List.ofFn (C.chunk ω)).take i).flatten)
      (C.chunk ω i) hpe
    have hP := (C.hP ω).le
    have hx : 0 ≤ C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten)
        (C.chunk ω i) pe := mul_nonneg hP hb
    calc lam * (C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten)
            (C.chunk ω i) pe)
        ≤ 1 * (C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take i).flatten)
            (C.chunk ω i) pe) := mul_le_mul_of_nonneg_right hlam1 hx
      _ = _ := one_mul _
  htotal := hT'

end ScaleTotal

end KServer

open KServer KServer.ScaleTotal

/-- **Mass normalisation.** The sizes of a chunk system with size floor zero
may be scaled down: for every target `T'` between `0` and the expected total
mass there is a chunk system on the same chunks whose expected total mass is
exactly `T'`. All the structural data — the chunk count, the filtration, the
chunks themselves, the size ceiling and the escape price — are unchanged, and
a Doob jump bound of the total mass is preserved. -/
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL) (hpe : 0 ≤ pe)
    (T' : ℝ) (hT0 : 0 ≤ T') (hT : T' ≤ ∑ ω, C.P ω * ∑ i, C.size ω i)
    {jb : ℝ} (hjb : C.DoobJumpBound jb) :
    ∃ C' : ChunkSystemB X s t 0 cB T' pe mL,
      C'.m = C.m ∧
      (∑ ω, C'.P ω * ∑ i, C'.size ω i) = T' ∧
      ((∀ ω₁ ω₂ : C.Ω, C.hist 0 ω₁ = C.hist 0 ω₂) →
        ∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) ∧
      C'.DoobJumpBound jb := by
  classical
  set E : ℝ := ∑ ω, C.P ω * ∑ i, C.size ω i with hE
  set lam : ℝ := if E = 0 then 0 else T' / E with hlam
  have hE0 : 0 ≤ E := by
    refine Finset.sum_nonneg fun ω _ => ?_
    have h1 : (0 : ℝ) ≤ ∑ i, C.size ω i :=
      Finset.sum_nonneg fun i _ => (C.hsize ω i).1
    have := (C.hP ω).le
    nlinarith
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    split
    · exact le_refl 0
    · exact div_nonneg hT0 hE0
  have hlam1 : lam ≤ 1 := by
    rw [hlam]
    split
    · norm_num
    · rename_i hne
      have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hne)
      rw [div_le_one hEpos]
      exact hT
  have hscale : ∀ ω : C.Ω, (∑ i, lam * C.size ω i) = lam * ∑ i, C.size ω i :=
    fun ω => by rw [Finset.mul_sum]
  have hsum : (∑ ω, C.P ω * ∑ i, lam * C.size ω i) = lam * E := by
    rw [hE, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [hscale ω]
    ring
  have hlamE : lam * E = T' := by
    rw [hlam]
    split
    · rename_i h
      have hle : T' ≤ 0 := by rw [h] at hT; exact hT
      have hz : T' = 0 := le_antisymm hle hT0
      rw [zero_mul, hz]
    · rename_i hne
      have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hne)
      field_simp
  have hT'le : T' ≤ ∑ ω, C.P ω * ∑ i, lam * C.size ω i := by
    rw [hsum, hlamE]
  refine ⟨scaled C lam T' hlam0 hlam1 hpe hT'le, rfl, ?_, fun h => h, fun h => h, ?_⟩
  · show (∑ ω, C.P ω * ∑ i, lam * C.size ω i) = T'
    rw [hsum, hlamE]
  · -- the Doob martingale of the scaled system is `lam` times the original one
    intro h ω
    have hts : ∀ ω' : C.Ω,
        (scaled C lam T' hlam0 hlam1 hpe hT'le).totalSize ω'
          = lam * C.totalSize ω' := by
      intro ω'
      show (∑ i, lam * C.size ω' i) = lam * ∑ i, C.size ω' i
      exact hscale ω'
    have hdoob : ∀ (n : ℕ) (ω' : C.Ω),
        (scaled C lam T' hlam0 hlam1 hpe hT'le).doobTotal n ω'
          = lam * C.doobTotal n ω' := by
      intro n ω'
      show (∑ ω'' ∈ C.atom n ω', C.P ω''
              * (scaled C lam T' hlam0 hlam1 hpe hT'le).totalSize ω'')
            / C.mass (C.atom n ω')
          = lam * ((∑ ω'' ∈ C.atom n ω', C.P ω'' * C.totalSize ω'')
            / C.mass (C.atom n ω'))
      rw [Finset.sum_congr rfl fun ω'' _ => by rw [hts ω'']]
      have hpull : ∑ ω'' ∈ C.atom n ω', C.P ω'' * (lam * C.totalSize ω'')
          = lam * ∑ ω'' ∈ C.atom n ω', C.P ω'' * C.totalSize ω'' := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω'' _ => by ring
      rw [hpull, mul_div_assoc]
    rw [hdoob (h + 1) ω, hdoob h ω, ← mul_sub, abs_mul, abs_of_nonneg hlam0]
    have := hjb h ω
    nlinarith [abs_nonneg (C.doobTotal (h + 1) ω - C.doobTotal h ω)]

