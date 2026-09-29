-- Prove2me | solution 1 for KServer.chunk_restrict_sturdy
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-10T11:30:26.745562+00:00
-- url     : https://prove2.me/submissions/4d86d8a9-3c8b-4967-b5fb-e9ba483553c0

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_adjust
import Definitions.Def_KServer_sturdy

namespace KServer

namespace RestrictSturdy

variable {X : Type*} [MetricSpace X]

/-- The partial cost of an evader on a chunk is nonnegative. -/
theorem costOn_nonneg (E : EvaderAlgorithm X) (h χ : List (Set X)) :
    0 ≤ E.costOn h χ := by
  unfold EvaderAlgorithm.costOn EvaderAlgorithm.cost
  have hsub : Finset.range h.length ⊆ Finset.range (h ++ χ).length := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    simp only [List.length_append]
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

/-- The system obtained by conditioning on the time-`n` atom of `ω₀` and
forgetting the mass of the first `n` chunks. -/
noncomputable def restrict (C : ChunkSystemB X s t 0 cB T pe mL) (hpe : 0 ≤ pe)
    (hcB : 0 ≤ cB) (n : ℕ) (ω₀ : C.Ω) (T' : ℝ)
    (hT' : T' ≤ (∑ ω ∈ C.atom n ω₀,
      C.P ω * ∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
        / C.mass (C.atom n ω₀)) :
    ChunkSystemB X s t 0 cB T' pe mL where
  Ω := {ω : C.Ω // ω ∈ C.atom n ω₀}
  instFin := inferInstance
  instDec := inferInstance
  P := fun ω => C.P ω.1 / C.mass (C.atom n ω₀)
  m := C.m
  hist := fun i ω => C.hist i ω.1
  chunk := fun ω => C.chunk ω.1
  size := fun ω i => if (i : ℕ) < n then 0 else C.size ω.1 i
  hP := fun ω => div_pos (C.hP ω.1) (C.mass_atom_pos n ω₀)
  hPsum := by
    have h1 : ∑ ω : {ω : C.Ω // ω ∈ C.atom n ω₀}, C.P ω.1 / C.mass (C.atom n ω₀)
        = (∑ ω ∈ C.atom n ω₀, C.P ω) / C.mass (C.atom n ω₀) := by
      rw [Finset.sum_div]
      exact Finset.sum_coe_sort (C.atom n ω₀) (fun ω => C.P ω / C.mass (C.atom n ω₀))
    rw [h1]
    exact div_self (ne_of_gt (C.mass_atom_pos n ω₀))
  hm := C.hm
  hm0 := C.hm0
  href := fun i j hij ω ω' h => C.href i j hij ω.1 ω'.1 h
  hadapt := fun i ω ω' h => C.hadapt i ω.1 ω'.1 h
  hsmeas := fun i ω ω' h => by
    by_cases hi : (i : ℕ) < n
    · simp [hi]
    · simp only [hi, if_false]
      exact C.hsmeas i ω.1 ω'.1 h
  hne := fun ω i => C.hne ω.1 i
  hlast := fun ω => C.hlast ω.1
  hopt := fun ω => C.hopt ω.1
  hsize := fun ω i => by
    by_cases hi : (i : ℕ) < n
    · simp [hi, hcB]
    · simp only [hi, if_false]
      exact ⟨(C.hsize ω.1 i).1, (C.hsize ω.1 i).2⟩
  hcost := by
    intro i ω₀' E bail
    have hmass := C.mass_atom_pos n ω₀
    -- rewrite both sides as sums over a `Finset C.Ω`
    have hset : (Finset.univ.filter
          (fun ω : {ω : C.Ω // ω ∈ C.atom n ω₀} => C.hist i ω.1 = C.hist i ω₀'.1))
        = Finset.univ.filter
          (fun ω : {ω : C.Ω // ω ∈ C.atom n ω₀} => C.hist i ω.1 = C.hist i ω₀'.1) := rfl
    have hsum : ∀ g : C.Ω → ℝ,
        (∑ ω ∈ Finset.univ.filter
            (fun ω : {ω : C.Ω // ω ∈ C.atom n ω₀} => C.hist i ω.1 = C.hist i ω₀'.1),
            g ω.1)
          = ∑ ω ∈ (C.atom n ω₀).filter (fun ω => C.hist i ω = C.hist i ω₀'.1), g ω := by
      intro g
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Finset.sum_coe_sort (C.atom n ω₀)
        (fun ω => if C.hist i ω = C.hist i ω₀'.1 then g ω else 0)
    by_cases hi : (i : ℕ) < n
    · -- the first `n` chunks carry no mass
      simp only [hi, if_true, zero_mul]
      refine Finset.sum_nonneg fun ω _ => ?_
      have hb := bailCost_nonneg E bail
        (((List.ofFn (C.chunk ω.1)).take (i : ℕ)).flatten) (C.chunk ω.1 i) hpe
      have hP : (0 : ℝ) ≤ C.P ω.1 / C.mass (C.atom n ω₀) :=
        le_of_lt (div_pos (C.hP ω.1) hmass)
      exact mul_nonneg hP hb
    · -- a later chunk: its atom is contained in the conditioning atom
      simp only [hi, if_false]
      have hfil : (C.atom n ω₀).filter (fun ω => C.hist i ω = C.hist i ω₀'.1)
          = C.atom i ω₀'.1 := by
        ext ω
        simp only [Finset.mem_filter, ChunkSystemB.mem_atom]
        constructor
        · rintro ⟨-, h2⟩; exact h2
        · intro h2
          refine ⟨?_, h2⟩
          have h3 : C.hist n ω = C.hist n ω₀'.1 :=
            C.href n i (by omega) ω ω₀'.1 h2
          exact h3.trans (C.mem_atom.mp ω₀'.2)
      have horig := C.hcost i ω₀'.1 E bail
      have hL : (∑ ω ∈ Finset.univ.filter
          (fun ω : {ω : C.Ω // ω ∈ C.atom n ω₀} => C.hist i ω.1 = C.hist i ω₀'.1),
            C.P ω.1 / C.mass (C.atom n ω₀))
          = (∑ ω ∈ C.atom i ω₀'.1, C.P ω) / C.mass (C.atom n ω₀) := by
        rw [hsum (fun ω => C.P ω / C.mass (C.atom n ω₀)), hfil, Finset.sum_div]
      have hR : (∑ ω ∈ Finset.univ.filter
          (fun ω : {ω : C.Ω // ω ∈ C.atom n ω₀} => C.hist i ω.1 = C.hist i ω₀'.1),
            C.P ω.1 / C.mass (C.atom n ω₀)
              * E.bailCost bail (((List.ofFn (C.chunk ω.1)).take (i : ℕ)).flatten)
                (C.chunk ω.1 i) pe)
          = (∑ ω ∈ C.atom i ω₀'.1, C.P ω
              * E.bailCost bail (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
                (C.chunk ω i) pe) / C.mass (C.atom n ω₀) := by
        rw [hsum (fun ω => C.P ω / C.mass (C.atom n ω₀)
          * E.bailCost bail (((List.ofFn (C.chunk ω)).take (i : ℕ)).flatten)
            (C.chunk ω i) pe), hfil, Finset.sum_div]
        exact Finset.sum_congr rfl fun ω _ => by ring
      rw [hL, hR]
      have hfilter : Finset.univ.filter (fun ω => C.hist i ω = C.hist i ω₀'.1)
          = C.atom i ω₀'.1 := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ChunkSystemB.mem_atom]
      rw [hfilter] at horig
      rw [mul_div_assoc' , div_le_div_iff_of_pos_right hmass]
      exact horig
  htotal := by
    refine le_trans hT' (le_of_eq ?_)
    rw [Finset.sum_div]
    exact (Finset.sum_coe_sort (C.atom n ω₀)
      (fun ω => C.P ω * (∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
        / C.mass (C.atom n ω₀))).symm.trans
      (Finset.sum_congr rfl fun ω _ => by ring)

end RestrictSturdy

end KServer

open KServer KServer.RestrictSturdy

/-- **Sturdiness by conditioning.** Every chunk system with size floor zero and
nonnegative escape price can be turned, for any depth `n`, into a chunk system
that is `L¹`-sturdy at depth `n` with defect `0` — its Doob martingale of the
total mass is constant up to time `n` — at the cost of at most `n · cB` of
expected total mass. One conditions on the time-`n` atom on which the
conditional expected total is largest and forgets the mass of the first `n`
chunks. -/
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (C : ChunkSystemB X s t 0 cB T pe mL)
    (hpe : 0 ≤ pe) (hcB : 0 ≤ cB) (n : ℕ) :
    ∃ C' : ChunkSystemB X s t 0 cB (T - n * cB) pe mL,
      C'.m = C.m ∧
      C'.SturdyL1 n 0 ∧
      (∀ ω₁ ω₂ : C'.Ω, C'.hist 0 ω₁ = C'.hist 0 ω₂) ∧
      ((∀ (ω : C.Ω) (i : Fin C.m), C.chunk ω i ≠ []) →
        ∀ (ω : C'.Ω) (i : Fin C'.m), C'.chunk ω i ≠ []) := by
  classical
  -- the sample space is nonempty
  have hΩ : Nonempty C.Ω := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h1 := C.hPsum
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨ω₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset C.Ω)
    (fun ω => C.condExp C.totalSize n ω) ⟨Classical.arbitrary C.Ω, Finset.mem_univ _⟩
  have hmass := C.mass_atom_pos n ω₀
  -- the conditional expected total on the chosen atom is at least the mean
  have hcond : (∑ ω, C.P ω * C.totalSize ω) ≤ C.condExp C.totalSize n ω₀ := by
    have h1 : (∑ ω, C.P ω * C.totalSize ω)
        = ∑ ω, C.P ω * C.condExp C.totalSize n ω := (C.sum_mul_condExp C.totalSize n).symm
    have h2 : ∑ ω, C.P ω * C.condExp C.totalSize n ω
        ≤ ∑ ω, C.P ω * C.condExp C.totalSize n ω₀ :=
      Finset.sum_le_sum fun ω _ =>
        mul_le_mul_of_nonneg_left (hmax ω (Finset.mem_univ ω)) (C.hP ω).le
    rw [h1]
    refine le_trans h2 (le_of_eq ?_)
    rw [← Finset.sum_mul, C.hPsum, one_mul]
  -- the mass of the first `n` chunks is at most `n * cB`
  have hpast : C.pastSize n ω₀ ≤ (n : ℝ) * cB := by
    have hcard : (Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < n)).card ≤ n := by
      have hsub : (Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < n)).image
          (fun i : Fin C.m => (i : ℕ)) ⊆ Finset.range n := by
        intro j hj
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨i, hi, rfl⟩ := hj
        exact Finset.mem_range.mpr hi
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_range] at h1
      exact h1
    have hle : C.pastSize n ω₀
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin C.m => (i : ℕ) < n), cB := by
      refine Finset.sum_le_sum fun i _ => (C.hsize ω₀ i).2
    refine le_trans hle ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hcB
  -- the conditioned system keeps enough mass
  have hkey : T - (n : ℝ) * cB
      ≤ (∑ ω ∈ C.atom n ω₀,
          C.P ω * ∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
        / C.mass (C.atom n ω₀) := by
    have hsplit : ∀ ω : C.Ω,
        (∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
          = C.totalSize ω - C.pastSize n ω := by
      intro ω
      have h1 : (∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
          = ∑ i ∈ Finset.univ.filter (fun i : Fin C.m => ¬ (i : ℕ) < n), C.size ω i := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => by
          by_cases h : (i : ℕ) < n <;> simp [h]
      rw [h1]
      unfold ChunkSystemB.totalSize ChunkSystemB.pastSize
      rw [eq_sub_iff_add_eq, add_comm]
      exact Finset.sum_filter_add_sum_filter_not Finset.univ _ _
    have hTt : T ≤ ∑ ω, C.P ω * C.totalSize ω := C.htotal
    have hnum : (∑ ω ∈ C.atom n ω₀,
          C.P ω * ∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
        = (∑ ω ∈ C.atom n ω₀, C.P ω * C.totalSize ω)
          - C.mass (C.atom n ω₀) * C.pastSize n ω₀ := by
      have h1 : (∑ ω ∈ C.atom n ω₀,
            C.P ω * ∑ i : Fin C.m, (if (i : ℕ) < n then 0 else C.size ω i))
          = ∑ ω ∈ C.atom n ω₀,
            (C.P ω * C.totalSize ω - C.P ω * C.pastSize n ω₀) := by
        refine Finset.sum_congr rfl fun ω hω => ?_
        rw [hsplit ω, C.pastSize_congr (C.mem_atom.mp hω)]
        ring
      rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    have hce : (∑ ω ∈ C.atom n ω₀, C.P ω * C.totalSize ω) / C.mass (C.atom n ω₀)
        = C.condExp C.totalSize n ω₀ := rfl
    have hcancel : C.mass (C.atom n ω₀) * C.pastSize n ω₀ / C.mass (C.atom n ω₀)
        = C.pastSize n ω₀ := by
      field_simp
    rw [hnum, sub_div, hce, hcancel]
    linarith [hcond, hpast, hTt]
  refine ⟨restrict C hpe hcB n ω₀ (T - (n : ℝ) * cB) hkey, rfl, ?_, ?_, fun h ω i => h ω.1 i⟩
  · -- sturdiness: the filtration is trivial up to depth `n`
    intro j hj
    set C' := restrict C hpe hcB n ω₀ (T - (n : ℝ) * cB) hkey with hC'
    have hatom : ∀ ω : C'.Ω, C'.atom j ω = Finset.univ := by
      intro ω
      ext ω'
      simp only [ChunkSystemB.mem_atom, Finset.mem_univ, iff_true]
      show C.hist j ω'.1 = C.hist j ω.1
      have h1 : C.hist n ω'.1 = C.hist n ω₀ := C.mem_atom.mp ω'.2
      have h2 : C.hist n ω.1 = C.hist n ω₀ := C.mem_atom.mp ω.2
      exact C.href j n hj ω'.1 ω.1 (h1.trans h2.symm)
    have hce : ∀ ω : C'.Ω, C'.condExp C'.totalSize j ω = C'.expTotal := by
      intro ω
      unfold ChunkSystemB.condExp ChunkSystemB.expTotal
      rw [hatom ω]
      have : C'.mass (Finset.univ : Finset C'.Ω) = 1 := C'.hPsum
      rw [this, div_one]
    refine le_of_eq (Finset.sum_eq_zero fun ω _ => ?_)
    rw [hce ω, sub_self, max_self, mul_zero]
  · intro ω₁ ω₂
    show C.hist 0 ω₁.1 = C.hist 0 ω₂.1
    have h1 : C.hist n ω₁.1 = C.hist n ω₀ := C.mem_atom.mp ω₁.2
    have h2 : C.hist n ω₂.1 = C.hist n ω₀ := C.mem_atom.mp ω₂.2
    exact C.href 0 n (Nat.zero_le n) ω₁.1 ω₂.1 (h1.trans h2.symm)
